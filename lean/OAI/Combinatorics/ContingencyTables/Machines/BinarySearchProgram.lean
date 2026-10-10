import OAI.Combinatorics.ContingencyTables.Machines.BoundedBinarySearch
import OAI.Combinatorics.ContingencyTables.Machines.NetworkFeasibilityProgram

namespace OAI

/-! # A polynomial binary program for monotone endpoint search

The supplied test is a realized binary predicate. The loop
performs one midpoint test per bit of the upper bound and keeps the
unchanged test data throughout.
-/

namespace ContingencyTables.BinarySearchProgram

open MatchingFPRAS.TreeTyped Polynomial BoundedBinarySearch

def midpointRealizer : Realizer midpoint :=
  composition (pair first (composition (pair
    (composition (composition (pair second first) subtract) successor) (constant 2)) quotient)) add

lemma polynomial_midpoint : PolynomialTime midpointRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair
      (polynomial_composition
        (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
          polynomial_subtract) polynomial_successor) (polynomial_constant 2))
      polynomial_quotient)) polynomial_add

variable {A : Type} [Codec A]
variable (test : A×ℕ→Bool) (T : Realizer test)

abbrev State (A : Type) := A×Window

def advance (z : ℕ×State A) : State A :=
  (z.2.1,step (fun t=>test (z.2.1,t)) z.2.2)

def advanceRealizer : Realizer (advance test) := by
  let M : Realizer (fun z : ℕ×State A=>midpoint z.2.2) :=
    composition (composition second second) midpointRealizer
  let P : Realizer (fun z : ℕ×State A=>test (z.2.1,midpoint z.2.2)) :=
    composition (f := fun z : ℕ×State A=>(z.2.1,midpoint z.2.2)) (g := test)
      (pair (composition second first) M) T
  let yes : Realizer (fun z : ℕ×State A=>(midpoint z.2.2,z.2.2.2)) :=
    pair M (composition (composition second second) second)
  let no : Realizer (fun z : ℕ×State A=>(z.2.2.1,midpoint z.2.2-1)) :=
    pair (composition (composition second second) first) (composition M predecessor)
  exact pair (composition second first) (choose P yes no)

lemma polynomial_advance (hT : PolynomialTime T) : PolynomialTime (advanceRealizer test T) := by
  unfold advanceRealizer
  apply polynomial_pair
  · exact polynomial_composition polynomial_second polynomial_first
  · apply polynomial_choose
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_first)
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_midpoint)) hT
    · exact polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_midpoint)
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_second)
    · exact polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_first)
        (polynomial_composition
          (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
            polynomial_midpoint) polynomial_predecessor)

lemma midpoint_le_max (p : Window) : midpoint p≤ max p.1 p.2 := by
  rcases p with ⟨lo,hi⟩
  unfold BoundedBinarySearch.midpoint
  omega

lemma step_le_max (f : ℕ→Bool) (p : Window) :
    (step f p).1≤ max p.1 p.2 ∧ (step f p).2≤ max p.1 p.2 := by
  have h := midpoint_le_max p
  unfold step
  split_ifs <;> dsimp only <;> constructor <;> omega

omit [Codec A] in
lemma fold_context (xs : List ℕ) (s : State A) :
    (xs.foldl (fun s i=>advance test (i,s)) s).1=s.1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih => exact ih (advance test (i,s))

omit [Codec A] in
lemma fold_bounds (xs : List ℕ) (s : State A) (M : ℕ)
    (h1 : s.2.1≤M) (h2 : s.2.2≤M) :
    (xs.foldl (fun s i=>advance test (i,s)) s).2.1≤M ∧
      (xs.foldl (fun s i=>advance test (i,s)) s).2.2≤M := by
  induction xs generalizing s with
  | nil => exact ⟨h1,h2⟩
  | cons i xs ih =>
    have h := step_le_max (fun t=>test (s.1,t)) s.2
    have hm : max s.2.1 s.2.2≤M := max_le h1 h2
    exact ih (advance test (i,s)) (h.1.trans hm) (h.2.trans hm)

lemma polynomial_loop (hT : PolynomialTime T) :
    PolynomialTime (fold (advanceRealizer test T)) := by
  apply polynomial_fold (polynomial_advance test T hT) (20*(X+1))
  intro xs s pre _post _he
  let S := weight (xs,s)
  let out := pre.foldl (fun s i=>advance test (i,s)) s
  have hs : weight s≤S := weight_snd (xs,s)
  have ha : weight s.1≤S := (weight_fst s).trans hs
  have hp : weight s.2≤S := (weight_snd s).trans hs
  have hM : weight (max s.2.1 s.2.2)≤S := by
    rcases le_total s.2.1 s.2.2 with h | h
    · rw [max_eq_right h]
      exact (weight_snd s.2).trans hp
    · rw [max_eq_left h]
      exact (weight_fst s.2).trans hp
  have hb := fold_bounds test pre s (max s.2.1 s.2.2) (le_max_left _ _) (le_max_right _ _)
  have h1 := weight_nat_small hb.1
  have h2 := weight_nat_small hb.2
  change weight out.2.1≤4*weight (max s.2.1 s.2.2)+1 at h1
  change weight out.2.2≤4*weight (max s.2.1 s.2.2)+1 at h2
  have hc : out.1=s.1 := fold_context test pre s
  have ho : weight out=weight out.1+weight out.2.1+weight out.2.2+2 := by
    change weight (out.1,(out.2.1,out.2.2))=_
    simp only [weight_prod]
    omega
  simp only [eval_mul,eval_ofNat,eval_add,eval_X,eval_one]
  change weight out≤20*(S+1)
  rw [ho,hc]
  omega

def steps (z : A×ℕ) : List ℕ := List.range z.2.size

def stepsRealizer : Realizer (steps (A := A)) :=
  composition (composition second bitSize) range

lemma polynomial_steps : PolynomialTime (stepsRealizer (A := A)) := by
  apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_bitSize) X
  intro z
  simp only [Function.comp_apply,eval_X]
  exact (size_le_weight z.2).trans (weight_snd z)

def prepare (z : A×ℕ) : List ℕ×State A := (steps z,(z.1,(0,z.2)))

def prepareRealizer : Realizer (prepare (A := A)) :=
  pair stepsRealizer (pair first (pair (constant 0) second))

lemma polynomial_prepare : PolynomialTime (prepareRealizer (A := A)) :=
  polynomial_pair polynomial_steps
    (polynomial_pair polynomial_first (polynomial_pair (polynomial_constant 0) polynomial_second))

def execute (z : A×ℕ) : State A :=
  (steps z).foldl (fun s i=>advance test (i,s)) (z.1,(0,z.2))

def executeRealizer : Realizer (execute test) :=
  composition (f := prepare (A := A))
    (g := fun z : List ℕ×State A=>z.1.foldl (fun s i=>advance test (i,s)) z.2)
    prepareRealizer (fold (advanceRealizer test T))

lemma polynomial_execute (hT : PolynomialTime T) : PolynomialTime (executeRealizer test T) :=
  polynomial_composition polynomial_prepare (polynomial_loop test T hT)

def search (z : A×ℕ) : ℕ := (execute test z).2.1

def searchRealizer : Realizer (search test) :=
  composition (f := execute test) (g := fun s : State A=>s.2.1)
    (executeRealizer test T) (composition second first)

lemma polynomial_search (hT : PolynomialTime T) : PolynomialTime (searchRealizer test T) :=
  polynomial_composition (polynomial_execute test T hT)
    (polynomial_composition polynomial_second polynomial_first)

omit [Codec A] in
lemma fold_code (xs : List ℕ) (a : A) (p : Window) :
    xs.foldl (fun s i=>advance test (i,s)) (a,p)=
      (a,run (fun t=>test (a,t)) xs.length p) := by
  induction xs generalizing p with
  | nil => rfl
  | cons i xs ih =>
    change xs.foldl (fun s i=>advance test (i,s))
      (a,step (fun t=>test (a,t)) p)=(a,run (fun t=>test (a,t)) (xs.length+1) p)
    exact ih _

omit [Codec A] in
theorem search_eq (a : A) (K U : ℕ)
    (ht : ∀ t,test (a,t)=true ↔ t≤K) (hK : K≤U) : search test (a,U)=K := by
  unfold search execute
  rw [fold_code]
  simp only [steps,List.length_range]
  exact congrArg Prod.fst (run_eq_cutoff _ K U U.size ht hK (Nat.lt_size_self U))

end ContingencyTables.BinarySearchProgram

end OAI
