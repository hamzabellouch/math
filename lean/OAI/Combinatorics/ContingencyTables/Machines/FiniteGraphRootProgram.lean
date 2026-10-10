import OAI.Combinatorics.ContingencyTables.Transport.FiniteGraphRoots
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileExchangeProgram
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialCollections
import OAI.Combinatorics.MatchingCount.Complexity.TreeChoiceCosts
import OAI.Combinatorics.MatchingCount.Machines.TreeColex
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPCounts

namespace OAI

/-! # A binary list program computing a component root

The graph is supplied by adjacency lists. The program makes one growth
round per stored vertex, then minimizes the reached indices. No loop
depends on the numeric size of an index or of an edge capacity.
-/

namespace ContingencyTables.FiniteGraphRootProgram

open MatchingFPRAS.TreeTyped Polynomial

abbrev GraphCode := List (List ℕ)
abbrev SearchState := GraphCode×List ℕ
abbrev Input := GraphCode×ℕ

def indices (rows : GraphCode) : List ℕ := List.range rows.length

def indicesRealizer : Realizer indices := composition listLength range

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange polynomial_listLength X
  intro rows
  simpa only [Function.comp_apply,eval_X] using list_length_le_weight rows

def neighborHit (z : List ℕ×List ℕ) : Bool :=
  z.2.any (fun a => decide (a∈z.1))

def neighborHitRealizer : Realizer neighborHit :=
  (composition (mapWith membership) any).congr (by
    intro z
    simp only [Function.comp_apply,List.any_map,Function.comp_def,id_eq,neighborHit])

lemma polynomial_neighborHit : PolynomialTime neighborHitRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_mapWith polynomial_membership) polynomial_any)

def growTest (z : SearchState×ℕ) : Bool :=
  decide (z.2∈z.1.2) || neighborHit (z.1.2,z.1.1.getD z.2 [])

def growTestRealizer : Realizer growTest :=
  composition (f := fun z : SearchState×ℕ =>
      (decide (z.2∈z.1.2),neighborHit (z.1.2,z.1.1.getD z.2 [])))
    (g := fun z : Bool×Bool => z.1 || z.2)
    (pair (composition (pair (composition first second) second) membership)
      (composition (pair (composition first second)
        (composition (pair (composition first first) second) (getDFast [])))
        neighborHitRealizer)) boolOr

lemma polynomial_growTest : PolynomialTime growTestRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_membership)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        (polynomial_getDFast []))) polynomial_neighborHit)) polynomial_boolOr

def grow (z : SearchState) : List ℕ :=
  (indices z.1).filter (fun a => growTest (z,a))

def growRealizer : Realizer grow :=
  composition (pair identity (composition first indicesRealizer))
    (filterWith growTestRealizer)

lemma polynomial_grow : PolynomialTime growRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_indices))
    (polynomial_filterWith polynomial_growTest)

def advance (z : List ℕ×SearchState) : SearchState :=
  (z.2.1,grow z.2)

def advanceRealizer : Realizer advance :=
  pair (composition second first)
    (composition (f := fun z : List ℕ×SearchState => z.2) (g := grow) second growRealizer)

lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition polynomial_second polynomial_grow)

lemma fold_first (steps : List (List ℕ)) (s : SearchState) :
    (steps.foldl (fun s row => advance (row,s)) s).1=s.1 := by
  induction steps generalizing s with
  | nil => rfl
  | cons row steps ih => exact ih (advance (row,s))

lemma grow_weight (s : SearchState) : weight (grow s)≤weight (indices s.1) :=
  weight_sublist (List.filter_sublist (p := fun a => growTest (s,a)) (l := indices s.1))

lemma fold_weight (steps : List (List ℕ)) (s : SearchState) :
    weight (steps.foldl (fun s row => advance (row,s)) s).2≤
      max (weight s.2) (weight (indices s.1)) := by
  induction steps generalizing s with
  | nil => exact le_max_left _ _
  | cons row steps ih =>
    have ht := ih (advance (row,s))
    have hs := grow_weight s
    exact ht.trans (max_le (hs.trans (le_max_right _ _)) (le_max_right _ _))

lemma indices_weight (rows : GraphCode) :
    weight (indices rows)≤rows.length*(4*rows.length+2)+1 := by
  have h := weight_map_bound (as := List.range rows.length) (f := id)
    (N := 4*rows.length+1) (by
      intro a ha
      exact (weight_nat_numeric a).trans (by
        have := List.mem_range.mp ha
        omega))
  simpa only [List.map_id,List.length_range,indices] using h

lemma polynomial_searchFold : PolynomialTime (fold advanceRealizer) := by
  apply polynomial_fold polynomial_advance (10*(X+1)^2)
  intro steps s pre _post _he
  let S := weight (steps,s)
  let out := pre.foldl (fun s row => advance (row,s)) s
  have hs : weight s≤S := weight_snd (steps,s)
  have hr : weight s.1≤S := (weight_fst s).trans hs
  have hv : weight s.2≤S := (weight_snd s).trans hs
  have hn : s.1.length≤S := (list_length_le_weight s.1).trans hr
  have hi := indices_weight s.1
  have hib : weight (indices s.1)≤4*S^2+2*S+1 := by
    have hm := Nat.mul_le_mul hn (show 4*s.1.length+2≤4*S+2 by omega)
    nlinarith
  have ho : weight out.2 ≤ max (weight s.2) (weight (indices s.1)) := fold_weight pre s
  have hot : weight out.2≤4*S^2+3*S+1 := ho.trans (max_le (by omega) (by omega))
  have hf : out.1=s.1 := fold_first pre s
  have hw : weight out=weight out.1+weight out.2+1 := by
    change weight (out.1,out.2)=_
    rw [weight_prod]
    omega
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change weight out≤10*(S+1)^2
  rw [hw,hf]
  nlinarith

def prepare (z : Input) : GraphCode×SearchState := (z.1,(z.1,[z.2]))

def prepareRealizer : Realizer prepare :=
  pair first (pair first (composition (pair second (constant [])) listCons))

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair polynomial_first (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant []))
      polynomial_listCons))

def run (z : Input) : SearchState :=
  z.1.foldl (fun s row => advance (row,s)) (z.1,[z.2])

def runRealizer : Realizer run := composition prepareRealizer (fold advanceRealizer)

lemma polynomial_run : PolynomialTime runRealizer :=
  polynomial_composition polynomial_prepare polynomial_searchFold

def reached (z : Input) : List ℕ := (run z).2

def reachedRealizer : Realizer reached :=
  composition (f := run) (g := fun s : SearchState => s.2) runRealizer second

theorem polynomial_reached : PolynomialTime reachedRealizer :=
  polynomial_composition polynomial_run polynomial_second

lemma minimum_fold_le (xs : List ℕ) (b : ℕ) :
    xs.foldl (fun b a => min a b) b≤b := by
  induction xs generalizing b with
  | nil => exact le_rfl
  | cons a xs ih => exact (ih (min a b)).trans (min_le_right _ _)

lemma polynomial_minimumFold : PolynomialTime (fold minimum) := by
  apply polynomial_fold polynomial_minimum (4*X+1)
  intro xs b pre _post _he
  have hb : b.size≤weight (xs,b) := (size_le_weight b).trans (weight_snd (xs,b))
  have hs := Nat.size_le_size (minimum_fold_le pre b)
  have hw := weight_nat_le (pre.foldl (fun b a => min a b) b)
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  omega

def rootCode (z : Input) : ℕ :=
  (reached z).foldl (fun b a => min a b) z.1.length

def rootCodeRealizer : Realizer rootCode :=
  composition (f := fun z : Input => (reached z,z.1.length))
    (g := fun z : List ℕ×ℕ => z.1.foldl (fun b a => min a b) z.2)
    (pair reachedRealizer (composition first listLength)) (fold minimum)

theorem polynomial_rootCode : PolynomialTime rootCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_reached
    (polynomial_composition polynomial_first polynomial_listLength)) polynomial_minimumFold

end ContingencyTables.FiniteGraphRootProgram

end OAI
