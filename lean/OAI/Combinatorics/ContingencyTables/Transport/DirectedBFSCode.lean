import OAI.Combinatorics.ContingencyTables.Transport.FiniteDirectedBFS
import Mathlib.Data.List.OfFn

namespace OAI

/-! # Materialized breadth-first path tables

Every round reads the preceding path table and writes one table of the
same size. Consequently evaluation does not recursively recompute old
rounds when different vertices ask for their predecessors.
-/

namespace ContingencyTables.DirectedBFSCode

abbrev Graph := List (List Bool)
abbrev Store := List (Option (List ℕ))

def adjacent (g : Graph) (u v : ℕ) : Bool := (g.getD u []).getD v false
def lookup (P : Store) (v : ℕ) : Option (List ℕ) := P.getD v none

def predecessor (g : Graph) (P : Store) (v : ℕ) : Option ℕ :=
  (List.range g.length).find? (fun u=>(lookup P u).isSome && adjacent g u v)

def roundRow (g : Graph) (P : Store) (v : ℕ) : Option (List ℕ) :=
  match lookup P v with
  | some xs => some xs
  | none => (predecessor g P v).bind (fun u=>(lookup P u).map (fun xs=>xs++[v]))

def round (g : Graph) (P : Store) : Store :=
  (List.range g.length).map (roundRow g P)

def initial (g : Graph) (s : ℕ) : Store :=
  (List.range g.length).map (fun v=>if v=s then some [s] else none)

def run (g : Graph) (s : ℕ) : Store :=
  (List.range g.length).foldl (fun P _=>round g P) (initial g s)

def search (g : Graph) (s t : ℕ) : Option (List ℕ) := lookup (run g s) t

def graphCode {n : ℕ} (E : Fin n → Fin n → Bool) : Graph :=
  List.ofFn (fun u=>List.ofFn (E u))

def storeCode {n : ℕ} (P : FiniteDirectedBFS.Paths n) : Store :=
  List.ofFn (fun u=>(P u).map (List.map Fin.val))

lemma range_eq_map (n : ℕ) : List.range n=(List.finRange n).map Fin.val := by
  apply List.ext_getElem <;> simp

lemma adjacent_graphCode {n : ℕ} (E : Fin n → Fin n → Bool) (u v : Fin n) :
    adjacent (graphCode E) u.val v.val=E u v := by
  simp [adjacent,graphCode,List.getD_eq_getElem?_getD,u.isLt,v.isLt]

lemma lookup_storeCode {n : ℕ} (P : FiniteDirectedBFS.Paths n) (v : Fin n) :
    lookup (storeCode P) v.val=(P v).map (List.map Fin.val) := by
  simp [lookup,storeCode,List.getD_eq_getElem?_getD,v.isLt]

lemma predecessor_code {n : ℕ} (E : Fin n → Fin n → Bool)
    (P : FiniteDirectedBFS.Paths n) (v : Fin n) :
    predecessor (graphCode E) (storeCode P) v.val=
      (FiniteDirectedBFS.predecessor E P v).map Fin.val := by
  have hlen : (graphCode E).length=n := by simp [graphCode]
  simp only [predecessor,hlen,range_eq_map,List.find?_map]
  congr 1
  apply congrArg (fun f=>(List.finRange n).find? f)
  funext u
  simp only [Function.comp_apply,lookup_storeCode,Option.isSome_map,adjacent_graphCode]

lemma roundRow_code {n : ℕ} (E : Fin n → Fin n → Bool)
    (P : FiniteDirectedBFS.Paths n) (v : Fin n) :
    roundRow (graphCode E) (storeCode P) v.val=
      (FiniteDirectedBFS.round E P v).map (List.map Fin.val) := by
  simp only [roundRow,lookup_storeCode,predecessor_code,FiniteDirectedBFS.round]
  cases hp : P v with
  | some xs => rfl
  | none =>
    cases hu : FiniteDirectedBFS.predecessor E P v with
    | none => rfl
    | some u =>
      simp only [Option.map_some,Option.bind_some,lookup_storeCode]
      cases hpu : P u <;> simp [List.map_append]

lemma round_code {n : ℕ} (E : Fin n → Fin n → Bool) (P : FiniteDirectedBFS.Paths n) :
    round (graphCode E) (storeCode P)=storeCode (FiniteDirectedBFS.round E P) := by
  simp only [round,graphCode,List.length_ofFn,range_eq_map,List.map_map]
  rw [←List.ofFn_eq_map]
  unfold storeCode
  apply congrArg List.ofFn
  funext v
  exact roundRow_code E P v

lemma initial_code {n : ℕ} (E : Fin n → Fin n → Bool) (s : Fin n) :
    initial (graphCode E) s.val=storeCode (FiniteDirectedBFS.paths E s 0) := by
  simp only [initial,graphCode,List.length_ofFn,range_eq_map,List.map_map]
  rw [←List.ofFn_eq_map]
  unfold storeCode
  apply congrArg List.ofFn
  funext v
  by_cases h : v=s
  · subst v; simp [FiniteDirectedBFS.paths]
  · have hv : v.val≠s.val := fun he=>h (Fin.ext he)
    simp [Function.comp_apply,FiniteDirectedBFS.paths,h,hv]

lemma fold_round_code {n : ℕ} (E : Fin n → Fin n → Bool) (s : Fin n) (k : ℕ) :
    (List.range k).foldl (fun P _=>round (graphCode E) P) (initial (graphCode E) s.val)=
      storeCode (FiniteDirectedBFS.paths E s k) := by
  induction k with
  | zero => simpa using initial_code E s
  | succ k ih =>
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,ih,round_code,FiniteDirectedBFS.paths]

theorem run_code {n : ℕ} (E : Fin n → Fin n → Bool) (s : Fin n) :
    run (graphCode E) s.val=storeCode (FiniteDirectedBFS.paths E s n) := by
  simpa only [run,graphCode,List.length_ofFn] using fold_round_code E s n

theorem search_code {n : ℕ} (E : Fin n → Fin n → Bool) (s t : Fin n) :
    search (graphCode E) s.val t.val=
      (FiniteDirectedBFS.paths E s n t).map (List.map Fin.val) := by
  rw [search,run_code,lookup_storeCode]

end ContingencyTables.DirectedBFSCode

end OAI
