#load "str.cma" ;;
exception NegativeNumber;;
exception NotFound ;;

(*	Formula è un record che contiene i dati necessari a rappresentare
*	una formula in cnf:
*	- numero dei letterali presenti  (sostituibile con List.len this.letterali)
*	- letterali [("A", 0);("D", 1);("B", 1);("C", 0)]
*	- clausole  [["A"; "B"; "!"; "C"]; ["D"; "!"; "A"]]
*)	
type formula = {
  numero_letterali: int;
  mutable letterali: (string * int) list;
  clausole:  (string list) list;
};; 


(*_________________________Init formula_________________________*)

(* "s" prende la formula da testare *)
let f_stringa = "(A)^(B)^(!BvC)^(!U)^(X)^(FvZ)^(Rv!CvD)^(!F)^(!BvC)^(XvB)^(!Xv!F)";;

(*let s = "(AvBv!C)^(Dv!A))^(Ev!A)^!A";;
let s = "(AvBv!C)^(Dv!A))^(Ev!A)^!A";;
let s = "(AvBv!C)^(Dv!A))^(Ev!A)^!A";;
*)

(* Rimuove un carattere (o sottostringa) sa una stringa*)
(* val rimuovi_carattere : string -> string -> string = <fun> *)
let rimuovi_carattere c =
    Str.global_replace (Str.regexp_string c ) ""
;;

(* Formatta la stringa s per il formato clausola, ogni clausola viene separata *)
(*val formatta_clausola : string -> string list = <fun>*)
let formatta_clausola s =
  Str.split (Str.regexp "\\^") 
  (String.uppercase
  (rimuovi_carattere "(" 
  (rimuovi_carattere ")" 
  (rimuovi_carattere "v" 
  (s)))))
;; 

(* Rimuove tutti i caratteri che non sono letterali *)
(*val solo_letterali : string -> string = <fun>*)
let solo_letterali s = 
   remove_cha "^" 
  (rimuovi_carattere "(" 
  (rimuovi_carattere ")"
  (rimuovi_carattere "!" 
  (rimuovi_carattere "v" 
  (s)))))
;; 

(* Data una stringa torna una lista formata dai caratteri della stringa*)
(*val explode : string -> string list = <fun>*)
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) ((String.sub s i 1) :: l) in
  exp (String.length s - 1) [] 
;;

(*crea una lista di liste di stringe, ogni lista di stringhe è una clausola 
ogni stringa è un letterale o lo sua negazione *)
(*val forma_clausole : string -> string list list = <fun>*)
let forma_clausole s =
  let rec claus formatted_s lis = match formatted_s with
    [] -> lis
    | x::rest -> explode x :: (claus rest lis)
  in 
  claus (formatta_clausola s) []
;;

(* Data una stringa CNF conta il numero di letterali distinti*)
(*val contalet : string -> int = <fun>*)
let contalet s = 
  let rec funnn counter y =  match y with
    | "" -> counter
    | _ -> funnn (counter+1) (rimuovi_carattere (String.sub y 0 1) y)
  in 
  funnn 0 (String.uppercase(solo_letterali s))
;;

(* Data una formula in NCF trova i letterali*)
(*val lit : string -> (string * int) list = <fun>*)
let lit s =
  let rec aux y lst = match y with 
    | "" -> lst
    | _ -> aux (rimuovi_carattere (String.sub y 0 1) y) ((String.sub y 0 1, 0)::lst)
  in
  aux (String.uppercase(solo_letterali s)) []
;;


(*Assegna*)

let cnf = {numero_letterali = (contalet f_stringa); letterali =(lit f_stringa); clausole = (forma_clausole f_stringa)};;


(*____________END__________Init formula_________________________*)


(*______________________Funzione euristica___________________________*)


(* Cerca la chiave k, restituisce v o NotFound*)
(*val cerca : 'a -> ('a * 'b) list -> 'b = <fun>*)
(* cerca: ’a -> (’a * ’b) list -> ’b *) 
let rec cerca k = function
  | [] -> raise NotFound
  | (k1,v)::rest -> if k = k1 then v
                    else cerca k rest
;;

(*  Prende calusola lista str, e set lista di int , torna true se la clausola è soddisfatat, false altrimenti*)
(*val compara : string list -> int = <fun>*)
let compara clausola = 
  let rec aux c s = match c with
    | []  -> 0
    | "!"::rest -> if cerca (List.hd rest) s = 1 then (aux (List.tl rest) s) else 1
    | l::rest -> if cerca l s = 0 then (aux rest s)
                else 1
  in aux clausola cnf.letterali
;;
(*  RICHIEDE: cerca *)

(* Dato un nodo n restituisce il set di valori binari propri del nodo*)
(*val set_valori : int -> int list = <fun>*)
let rec set_valori n = 
  let rec aux n l set = match l with
    | 0 -> set
    | _ -> aux (n/2) (l-1) ((n mod 2)::set) 
  in aux n cnf.numero_letterali []
;;

(* Assegna un set di valori s al dizionario *)
(* val assegn_valore_chiave : 'a list -> ('b * 'a) list -> ('b * 'a) list = <fun>*)
let rec assegn_valore_chiave set d = match d with
  | [] -> d
  | (k,v1)::dict -> (k,(List.hd set))::(assegn_valore_chiave (List.tl set) dict)
;;

(*  Funzione euristica: Prende un nodo e utilizza formula, restituisce 
* la differenza tra il numero totale di clausole e quelle soddisfatte dallo 
* set di valori dei letterali del nodo. Per N clausole: N se nessuna è soddisfatta, 
* 0 se tutte sono soddisfatte 
*)
(*val f_heuristica : int -> int = <fun>*)
let f_heuristica n = 
(*  Assegna ai letterali della formula il set di valori al nodo n*) 
  let w = cnf.letterali <- (assegn_valore_chiave (set_valori n) cnf.letterali) in
  let rec aux clus h_val c_tot = match clus with
  |[] -> c_tot - h_val
  |cl::cls -> aux cls  (h_val+(compara cl)) (c_tot+1)
in aux cnf.clausole 0 0
;;
(*  RICHIEDE: formula; assegn_valore_chiave; set_valori; compara*)

(*________END__________Funzione euristica___________________________*)


(*_____________________Ricerca______________________________________*)

(*val powTA : int * int * int -> int = <fun>*)
let rec powTA (m, n, acc) = 
  if m = 0 then acc
  else powTA (m-1,n,(acc*n))
;;

(* Funzione elevamento a potenza*)
(*val pow : int * int -> int = <fun>*)
let pow (m, n) =
  if m < 0 then raise NegativeNumber 
  else powTA(n, m, 1)
;;

(* Restituisce l'intero di divisioni successive*)
(*val intero : int * int -> int = <fun>*)
let rec intero (x,c) = match c with
  |  0 -> x
  | _ -> intero (x/2, c-1)
;;

(*Restituisce un nodo connesso ad x *)
(*val next_n : int * int -> int = <fun>*)
let next_n (x,c) = 
  if (intero (x, c) mod 2) = 0 then (x + pow (2, c)) 
  else (x - pow (2, c))
;;

(* Dato un nodo trova i nodi adiacenti
 * Il grafo viene rappresentato da questa funzione*)
(*val adiacenti_di : int -> int list = <fun>*)
let adiacenti_di x =
  let rec aux y lst = match y with 
    | 0 -> lst
    | _ -> aux (y-1) ((next_n (x, y-1))::lst)
  in aux cnf.numero_letterali []
;;

(*  Inserisce value in lista l ordinandolo rispetto al valore di heuristica*)
(*val inserisci : int -> int list -> int list = <fun>*)
let rec inserisci value lis = match lis with
  | [] -> value::lis
  | hd::tail -> if (f_heuristica value) > (f_heuristica (List.hd lis)) then hd::(inserisci value tail)
                else value::lis
;;

(*  Inserisce ogni nodo della lista l2 nella lista l1 *)
(*val merge_in_ordine : int list -> int list -> int list = <fun>*)
let rec merge_in_ordine l1 l2 = match l2 with
  | [] -> l1
  | n::nodi -> merge_in_ordine (inserisci n l1) nodi
;; 

(*  Controlla se il nodo n è un nodo obiettivo*)
(*val goal : int -> bool = <fun>*)
let goal n =
  if f_heuristica n = 0 then true
  else false
;;  

(* Stampa il risulato con il set di valori che soddisfano la formula*)
(*val stampa_risultato : int -> string = <fun>*)
let stampa_risultato nodo =
  "\n\nLa formula è soddisfacibile con un set di valori \n\n"^
  let rec stampa_valori = function 
    [] -> "    nodo associato : "^ string_of_int nodo^"\n\n"
    | (s,n)::tail -> s^":"^(string_of_int n)^"  "^ stampa_valori tail
  in stampa_valori cnf.letterali
;;

(* Stampa set di valori al noodo corrente*)
(*val stampa_risultato_parziale : int -> string = <fun>*)
let stampa_risultato_parziale nodo =
  let rec stampa_valori = function 
    [] -> "      nodo associato : "^ string_of_int nodo ^"\n"
    | (s,n)::tail -> (string_of_int n)^"  "^ stampa_valori tail
  in stampa_valori cnf.letterali
;;

(* Stapa un messaggio in caso di terminazione senza soluzione*)
let stampa_fail =
  "\n\nNon ci sono assegnazioni valide, la formula\n\tF: "^s^"\nnon è soddisfacibile\n\n"
;;

(* Funzione di ricerca best-first termina se viene trovato un goal
 * o se tutti i nodi del grafo vengono visitati
*)
let bf_search_soddisfacibilita =
  let rec ricerca scoperti visitati  = 
    if scoperti = [] then (print_string stampa_fail;false)
    else 
      let nodo = List.hd scoperti in 
      if goal nodo then (print_string (stampa_risultato nodo); true)
      else
      ricerca (
        merge_in_ordine (List.tl scoperti) (
        let rec aux nodi_vicini = match nodi_vicini with
          | [] -> (print_string (stampa_risultato_parziale nodo));nodi_vicini
          | n::odi -> if ((not (List.mem n scoperti)) && 
                          (not (List.mem n visitati))) 
                      then n::(aux odi)
                      else aux odi
        in aux (adiacenti_di nodo)
        )
      ) (nodo::visitati)
in ricerca [0] []
;;