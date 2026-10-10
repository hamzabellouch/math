import Mathlib
import OAI.Computability.MaxCut.Encoding.ThreeBitTest

namespace OAI

/-! Explicit half-table storage, odd folding, and conditioning on the finite
set of satisfying local assignments for Håstad's test. -/

noncomputable section

namespace MaxCutGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

def cubeFlip (f : Cube I) : Cube I := fun i => !(f i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem cubeFlip_cubeFlip (f : Cube I) : cubeFlip (cubeFlip f) = f := by
  funext i
  simp [cubeFlip]

@[simp] theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

theorem sum_cubeFlip (F : Cube I → ℝ) : (∑ f, F (cubeFlip f)) = ∑ f, F f := by
  refine Finset.sum_bij (fun f _ => cubeFlip f) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ g _ h
    have h' := congrArg cubeFlip h
    simpa only [cubeFlip_cubeFlip] using h'
  · intro g _
    exact ⟨cubeFlip g, Finset.mem_univ _, cubeFlip_cubeFlip g⟩
  · intro f _
    rfl

theorem coefficient_zero_of_odd (F : Cube I → ℝ)
    (hF : ∀ f, F (cubeFlip f) = -F f) :
    coefficient F (fun _ => false) = 0 := by
  have hs : (∑ f, F f) = 0 := by
    have h := sum_cubeFlip F
    simp_rw [hF, Finset.sum_neg_distrib] at h
    linarith
  simp [coefficient, walsh, bitSign, Fintype.expect_eq_sum_div_card, hs]

theorem coefficient_sign_zero_of_folded (A : Cube I → Bool)
    (hA : ∀ f, A (cubeFlip f) = !(A f)) :
    coefficient (fun f => bitSign (A f)) (fun _ => false) = 0 := by
  apply coefficient_zero_of_odd
  intro f
  rw [hA, bitSign_not]

def representative (i₀ : I) (f : Cube I) : Cube I :=
  if f i₀ then cubeFlip f else f

omit [Fintype I] [DecidableEq I] in
theorem representative_at (i₀ : I) (f : Cube I) :
    representative i₀ f i₀ = false := by
  cases hf : f i₀ <;> simp [representative, cubeFlip, hf]

omit [Fintype I] [DecidableEq I] in
theorem representative_flip (i₀ : I) (f : Cube I) :
    representative i₀ (cubeFlip f) = representative i₀ f := by
  cases hf : f i₀ <;> simp [representative, cubeFlip, hf]

abbrev HalfCube (i₀ : I) := {f : Cube I // f i₀ = false}

def canonicalInput (i₀ : I) (f : Cube I) : HalfCube i₀ :=
  ⟨representative i₀ f, representative_at i₀ f⟩

omit [Fintype I] [DecidableEq I] in
theorem canonicalInput_flip (i₀ : I) (f : Cube I) :
    canonicalInput i₀ (cubeFlip f) = canonicalInput i₀ f := by
  apply Subtype.ext
  exact representative_flip i₀ f

/-- One stored bit and one explicit sign correction for every queried table. -/
def foldedAnswer (i₀ : I) (table : HalfCube i₀ → Bool) (f : Cube I) : Bool :=
  table (canonicalInput i₀ f) ^^ f i₀

omit [Fintype I] [DecidableEq I] in
theorem foldedAnswer_flip (i₀ : I) (table : HalfCube i₀ → Bool) (f : Cube I) :
    foldedAnswer i₀ table (cubeFlip f) = !(foldedAnswer i₀ table f) := by
  unfold foldedAnswer
  rw [canonicalInput_flip]
  change (table (canonicalInput i₀ f) ^^ !(f i₀)) =
    !(table (canonicalInput i₀ f) ^^ f i₀)
  cases table (canonicalInput i₀ f) <;> cases f i₀ <;> rfl

theorem foldedAnswer_zero_coefficient (i₀ : I) (table : HalfCube i₀ → Bool) :
    coefficient (fun f => bitSign (foldedAnswer i₀ table f)) (fun _ => false) = 0 :=
  coefficient_sign_zero_of_folded _ (foldedAnswer_flip i₀ table)

omit [Fintype I] [DecidableEq I] in
theorem foldedAnswer_dictator (i₀ i : I) (f : Cube I) :
    foldedAnswer i₀ (fun h => h.val i) f = f i := by
  cases hf : f i₀ <;> cases hi : f i <;>
    simp [foldedAnswer, canonicalInput, representative, cubeFlip, hf, hi]

def coordinateMask (i : I) : Cube I := fun j => decide (j = i)

def cubeToggle (i : I) (f : Cube I) : Cube I :=
  cubeXor f (coordinateMask i)

omit [Fintype I] in
@[simp] theorem cubeToggle_twice (i : I) (f : Cube I) :
    cubeToggle i (cubeToggle i f) = f := by
  funext j
  change ((f j ^^ coordinateMask i j) ^^ coordinateMask i j) = f j
  cases f j <;> cases coordinateMask i j <;> rfl

theorem walsh_coordinateMask (s : Cube I) (i : I) :
    walsh s (coordinateMask i) = bitSign (s i) := by
  unfold walsh
  rw [Finset.prod_eq_single i]
  · simp [coordinateMask]
  · intro j _ hj
    simp [coordinateMask, hj, bitSign]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem walsh_cubeToggle (s : Cube I) (i : I) (f : Cube I) (hs : s i = true) :
    walsh s (cubeToggle i f) = -walsh s f := by
  rw [cubeToggle, walsh_xor, walsh_coordinateMask, hs]
  simp [bitSign]

theorem sum_cubeToggle (i : I) (F : Cube I → ℝ) :
    (∑ f, F (cubeToggle i f)) = ∑ f, F f := by
  refine Finset.sum_bij (fun f _ => cubeToggle i f) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ g _ h
    have h' := congrArg (cubeToggle i) h
    simpa only [cubeToggle_twice] using h'
  · intro g _
    exact ⟨cubeToggle i g, Finset.mem_univ _, cubeToggle_twice i g⟩
  · intro f _
    rfl

def restrictQuery (valid : I → Bool) (f : Cube I) :
    Cube {i : I // valid i = true} := fun i => f i.val

omit [Fintype I] in
theorem restrictQuery_cubeToggle (valid : I → Bool) (i : I)
    (hi : valid i = false) (f : Cube I) :
    restrictQuery valid (cubeToggle i f) = restrictQuery valid f := by
  funext j
  have hj : j.val ≠ i := by
    intro heq
    have hp := j.property
    rw [heq, hi] at hp
    contradiction
  simp [restrictQuery, cubeToggle, cubeXor, coordinateMask, hj]

theorem conditioned_coefficient_zero_invalid (valid : I → Bool)
    (B : Cube {i : I // valid i = true} → ℝ) (s : Cube I) (i : I)
    (hi : valid i = false) (hs : s i = true) :
    coefficient (fun f => B (restrictQuery valid f)) s = 0 := by
  have hsum := sum_cubeToggle i (fun f => B (restrictQuery valid f) * walsh s f)
  simp_rw [restrictQuery_cubeToggle valid i hi, walsh_cubeToggle s i _ hs,
    mul_neg, Finset.sum_neg_distrib] at hsum
  have hz : (∑ f, B (restrictQuery valid f) * walsh s f) = 0 := by linarith
  simp [coefficient, Fintype.expect_eq_sum_div_card, hz]

/-- Every coordinate returned from a nonzero conditioned Fourier mask is an
actual valid local assignment, proved from the concrete restriction map. -/
theorem conditioned_coefficient_support (valid : I → Bool)
    (B : Cube {i : I // valid i = true} → ℝ) (s : Cube I)
    (hne : coefficient (fun f => B (restrictQuery valid f)) s ≠ 0) :
    ∀ i ∈ support s, valid i = true := by
  intro i hi
  have hs := (Finset.mem_filter.mp hi).2
  cases hv : valid i
  · exact False.elim (hne (conditioned_coefficient_zero_invalid valid B s i hv hs))
  · rfl

def conditionedFoldedAnswer (valid : I → Bool) (i₀ : {i : I // valid i = true})
    (table : HalfCube i₀ → Bool) (f : Cube I) : Bool :=
  foldedAnswer i₀ table (restrictQuery valid f)

omit [Fintype I] [DecidableEq I] in
theorem conditionedFoldedAnswer_flip (valid : I → Bool)
    (i₀ : {i : I // valid i = true}) (table : HalfCube i₀ → Bool) (f : Cube I) :
    conditionedFoldedAnswer valid i₀ table (cubeFlip f) =
      !(conditionedFoldedAnswer valid i₀ table f) := by
  change foldedAnswer i₀ table (cubeFlip (restrictQuery valid f)) = _
  exact foldedAnswer_flip i₀ table (restrictQuery valid f)

theorem conditionedFoldedAnswer_zero_coefficient (valid : I → Bool)
    (i₀ : {i : I // valid i = true}) (table : HalfCube i₀ → Bool) :
    coefficient (fun f => bitSign (conditionedFoldedAnswer valid i₀ table f))
      (fun _ => false) = 0 :=
  coefficient_sign_zero_of_folded _ (conditionedFoldedAnswer_flip valid i₀ table)

omit [Fintype I] [DecidableEq I] in
theorem conditionedFoldedAnswer_dictator (valid : I → Bool)
    (i₀ i : {i : I // valid i = true}) (f : Cube I) :
    conditionedFoldedAnswer valid i₀ (fun h => h.val i) f = f i.val := by
  exact foldedAnswer_dictator i₀ i (restrictQuery valid f)

end MaxCutGames.Foundations.Hastad
end

namespace MaxCutGames.Reduction.CloneGap

variable {α β : Type*}

def cart (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun x => ys.map fun y => (x, y)

theorem count_const (xs : List α) (b : Bool) :
    xs.countP (fun _ => b) = if b then xs.length else 0 := by
  cases b <;> simp

theorem count_cart (xs : List α) (ys : List β) (p : α → Bool) (q : β → Bool) :
    (cart xs ys).countP (fun z => p z.1 && q z.2) =
      xs.countP p * ys.countP q := by
  induction xs with
  | nil => simp [cart]
  | cons x xs ih =>
      simp only [cart, List.flatMap_cons, List.countP_append] at *
      rw [ih]
      cases h : p x <;>
        simp [List.countP_map, Function.comp_def, h, Nat.add_mul, Nat.add_comm]

theorem length_cart (xs : List α) (ys : List β) :
    (cart xs ys).length = xs.length * ys.length := by
  have := count_cart xs ys (fun _ => true) (fun _ => true)
  simpa using this

theorem count_cart_left (xs : List α) (ys : List β) (p : α → Bool) :
    (cart xs ys).countP (fun z => p z.1) = xs.countP p * ys.length := by
  simpa using count_cart xs ys p (fun _ => true)

theorem count_cart_right (xs : List α) (ys : List β) (p : β → Bool) :
    (cart xs ys).countP (fun z => p z.2) = xs.length * ys.countP p := by
  simpa using count_cart xs ys (fun _ => true) p

theorem count_cart_le (xs : List α) (ys : List β) (p : α × β → Bool)
    (bound : Nat) (h : ∀ x ∈ xs, ys.countP (fun y => p (x, y)) ≤ bound) :
    (cart xs ys).countP p ≤ xs.length * bound := by
  induction xs with
  | nil => simp [cart]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [cart, List.flatMap_cons, List.countP_append, List.countP_map,
        Function.comp_def] at *
      simp only [List.length_cons, Nat.add_mul]
      omega

theorem count_union_le (xs : List α) (p q : α → Bool) :
    xs.countP (fun x => p x || q x) ≤ xs.countP p + xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases hp : p x <;> cases hq : q x <;>
        simp [hp, hq] at * <;> omega

theorem count_remove (xs : List α) (p q : α → Bool) :
    xs.countP p ≤ xs.countP (fun x => p x && !q x) + xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases hp : p x <;> cases hq : q x <;>
        simp [hp, hq] at * <;> omega

abbrev Index := Nat
def indices : List Index := List.range 48
def triples : List (Index × Index × Index) := cart indices (cart indices indices)
def collision (t : Index × Index × Index) : Bool :=
  (t.1 == t.2.1) || (t.1 == t.2.2) || (t.2.1 == t.2.2)
def distinctTriples : List (Index × Index × Index) := triples.filter (fun t => !collision t)

theorem length_indices : indices.length = 48 := by simp [indices]
theorem length_triples : triples.length = 110592 := by
  simp [triples, length_cart, length_indices]

theorem count_index_eq_le (i : Index) : indices.countP (fun j => i == j) ≤ 1 := by
  have h := List.count_range (a := i) (n := 48)
  have heq : (fun j => i == j) = (fun j => j == i) := by
    funext j
    exact Bool.beq_comm
  rw [heq]
  change (List.range 48).count i ≤ 1
  rw [h]
  split <;> omega

theorem count_collision_le : triples.countP collision ≤ 6912 := by
  have h12 : triples.countP (fun t => t.1 == t.2.1) ≤ 2304 := by
    apply count_cart_le indices (cart indices indices) _ 48
    intro i _
    change (cart indices indices).countP (fun y => i == y.1) ≤ 48
    rw [count_cart_left indices indices (fun j => i == j), length_indices]
    have := count_index_eq_le i
    omega
  have h13 : triples.countP (fun t => t.1 == t.2.2) ≤ 2304 := by
    apply count_cart_le indices (cart indices indices) _ 48
    intro i _
    change (cart indices indices).countP (fun y => i == y.2) ≤ 48
    rw [count_cart_right indices indices (fun j => i == j), length_indices]
    have := count_index_eq_le i
    omega
  have h23 : triples.countP (fun t => t.2.1 == t.2.2) ≤ 2304 := by
    change (cart indices (cart indices indices)).countP (fun t => t.2.1 == t.2.2) ≤ 2304
    rw [count_cart_right indices (cart indices indices) (fun t => t.1 == t.2), length_indices]
    have h : (cart indices indices).countP (fun t => t.1 == t.2) ≤ 48 := by
      apply count_cart_le indices indices _ 1
      intro i _
      exact count_index_eq_le i
    omega
  have hA := count_union_le triples (fun t => t.1 == t.2.1) (fun t => t.1 == t.2.2)
  have hB := count_union_le triples
    (fun t => (t.1 == t.2.1) || (t.1 == t.2.2)) (fun t => t.2.1 == t.2.2)
  unfold collision
  omega

theorem majority_exists (g : Index → Bool) :
    ∃ b : Bool, 24 ≤ indices.countP (fun i => g i == b) := by
  have h := List.length_eq_countP_add_countP g (l := indices)
  have hn : (fun i => decide (¬g i = true)) = (fun i => !g i) := by
    funext i
    cases g i <;> rfl
  rw [hn] at h
  rw [length_indices] at h
  by_cases ht : 24 ≤ indices.countP g
  · exact ⟨true, by simpa using ht⟩
  · refine ⟨false, ?_⟩
    have : 24 ≤ indices.countP (fun i => !g i) := by omega
    simpa using this

def allAgree (p q r : Index → Bool) (t : Index × Index × Index) : Bool :=
  p t.1 && (q t.2.1 && r t.2.2)

theorem count_agree_distinct (p q r : Index → Bool)
    (hp : 24 ≤ indices.countP p) (hq : 24 ≤ indices.countP q)
    (hr : 24 ≤ indices.countP r) :
    6912 ≤ distinctTriples.countP (allAgree p q r) := by
  have hprod := count_cart indices (cart indices indices) p
    (fun t => q t.1 && r t.2)
  rw [count_cart] at hprod
  have h1 : 24 * 24 ≤ indices.countP q * indices.countP r := Nat.mul_le_mul hq hr
  have h2 : 24 * (24 * 24) ≤ indices.countP p *
      (indices.countP q * indices.countP r) := Nat.mul_le_mul hp h1
  have hremove := count_remove triples (allAgree p q r) collision
  have hcollision := count_collision_le
  change triples.countP (allAgree p q r) = _ at hprod
  unfold distinctTriples
  rw [List.countP_filter]
  omega

structure Equation (Name : Type) where
  first : Name
  second : Name
  third : Name
  rhs : Bool

variable {Name : Type}

def satisfied (e : Equation Name) (g : Name → Bool) : Bool :=
  (xor (xor (g e.first) (g e.second)) (g e.third)) == e.rhs

def clone (e : Equation Name) (t : Index × Index × Index) : Equation (Name × Index) :=
  ⟨(e.first, t.1), (e.second, t.2.1), (e.third, t.2.2), e.rhs⟩

theorem lift_preserves (e : Equation Name) (t : Index × Index × Index) (g : Name → Bool) :
    satisfied (clone e t) (fun z => g z.1) = satisfied e g := rfl

theorem clone_names_distinct (e : Equation Name) (t : Index × Index × Index)
    (h : collision t = false) :
    (clone e t).first ≠ (clone e t).second ∧
    (clone e t).first ≠ (clone e t).third ∧
    (clone e t).second ≠ (clone e t).third := by
  simp only [collision, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  dsimp [clone]
  exact ⟨fun he => h.1.1 (congrArg Prod.snd he),
    fun he => h.1.2 (congrArg Prod.snd he),
    fun he => h.2 (congrArg Prod.snd he)⟩

theorem agree_failure (e : Equation Name) (g : Name × Index → Bool)
    (majority : Name → Bool) (t : Index × Index × Index)
    (hfail : satisfied e majority = false)
    (h : allAgree (fun i => g (e.first, i) == majority e.first)
      (fun i => g (e.second, i) == majority e.second)
      (fun i => g (e.third, i) == majority e.third) t = true) :
    satisfied (clone e t) g = false := by
  simp only [allAgree, Bool.and_eq_true, beq_iff_eq] at h
  simpa [satisfied, clone, h.1, h.2.1, h.2.2] using hfail

theorem failed_occurrence_clones (e : Equation Name) (g : Name × Index → Bool)
    (majority : Name → Bool)
    (hmaj : ∀ v, 24 ≤ indices.countP (fun i => g (v, i) == majority v))
    (hfail : satisfied e majority = false) :
    6912 ≤ distinctTriples.countP (fun t => !satisfied (clone e t) g) := by
  have h := count_agree_distinct
    (fun i => g (e.first, i) == majority e.first)
    (fun i => g (e.second, i) == majority e.second)
    (fun i => g (e.third, i) == majority e.third)
    (hmaj _) (hmaj _) (hmaj _)
  apply Nat.le_trans h
  apply List.countP_mono_left
  intro t _ ht
  have hf := agree_failure e g majority t hfail ht
  simp [hf]

def majorityBit (g : Index → Bool) : Bool := decide (24 ≤ indices.countP g)

theorem majorityBit_count (g : Index → Bool) :
    24 ≤ indices.countP (fun i => g i == majorityBit g) := by
  have h := List.length_eq_countP_add_countP g (l := indices)
  have hn : (fun i => decide (¬g i = true)) = (fun i => !g i) := by
    funext i
    cases g i <;> rfl
  rw [hn, length_indices] at h
  by_cases ht : 24 ≤ indices.countP g
  · simp [majorityBit, ht]
  · have hn : 24 ≤ indices.countP (fun i => !g i) := by omega
    simpa [majorityBit, ht] using hn

def cloneList (source : List (Equation Name)) : List (Equation (Name × Index)) :=
  source.flatMap fun e => distinctTriples.map (clone e)

theorem length_cloneList (source : List (Equation Name)) :
    (cloneList source).length = source.length * distinctTriples.length := by
  induction source with
  | nil => simp [cloneList]
  | cons e es ih =>
      simp only [cloneList, List.flatMap_cons, List.length_append, List.length_map] at *
      rw [ih]
      simp [Nat.add_mul, Nat.add_comm]

theorem cloneList_failure_lower (source : List (Equation Name))
    (g : Name × Index → Bool) (majority : Name → Bool)
    (hmaj : ∀ v, 24 ≤ indices.countP (fun i => g (v, i) == majority v)) :
    6912 * source.countP (fun e => !satisfied e majority) ≤
      (cloneList source).countP (fun e => !satisfied e g) := by
  induction source with
  | nil => simp [cloneList]
  | cons e es ih =>
      simp only [cloneList, List.flatMap_cons, List.countP_append,
        List.countP_map, Function.comp_def] at *
      cases hf : satisfied e majority with
      | false =>
          have he := failed_occurrence_clones e g majority hmaj hf
          simp [hf, Nat.mul_add] at *
          omega
      | true =>
          simp [hf]
          omega

theorem clone_gap (source : List (Equation Name))
    (source_gap : ∀ A : Name → Bool,
      source.length ≤ 4 * source.countP (fun e => !satisfied e A))
    (g : Name × Index → Bool) :
    (cloneList source).length ≤
      64 * (cloneList source).countP (fun e => !satisfied e g) := by
  let majority : Name → Bool := fun v => majorityBit (fun i => g (v, i))
  have hmaj : ∀ v, 24 ≤ indices.countP (fun i => g (v, i) == majority v) :=
    fun v => majorityBit_count (fun i => g (v, i))
  have hlocal := cloneList_failure_lower source g majority hmaj
  have hsource := source_gap majority
  have hd : distinctTriples.length ≤ 110592 := by
    exact Nat.le_trans (List.length_filter_le _ triples) (by simp [length_triples])
  rw [length_cloneList]
  have hlength := Nat.mul_le_mul_left source.length hd
  have hs := Nat.mul_le_mul_right 27648 hsource
  have hc := Nat.mul_le_mul_left 64 hlocal
  omega

theorem clone_completeness_count (source : List (Equation Name)) (A : Name → Bool) :
    (cloneList source).countP (fun e => satisfied e (fun z => A z.1)) =
      source.countP (fun e => satisfied e A) * distinctTriples.length := by
  induction source with
  | nil => simp [cloneList]
  | cons e es ih =>
      simp only [cloneList, List.flatMap_cons, List.countP_append,
        List.countP_map, Function.comp_def] at *
      rw [ih]
      have he : (fun t => satisfied (clone e t) (fun z => A z.1)) =
          (fun _ => satisfied e A) := by
        funext t
        exact lift_preserves e t A
      rw [he, count_const]
      cases h : satisfied e A <;> simp [h, Nat.add_mul, Nat.add_comm]

end MaxCutGames.Reduction.CloneGap

namespace MaxCutGames.Foundations.Hastad.FoldedEquation

open MaxCutGames.Reduction.CloneGap
open scoped BigOperators

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Left and right stored tables have disjoint variable names. -/
abbrev Address (i₀ : I) (j₀ : J) := HalfCube i₀ ⊕ HalfCube j₀

def storedAssignment {i₀ : I} {j₀ : J}
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) :
    Address i₀ j₀ → Bool := Sum.elim tableA tableB

/-- Cancellation of the two copies of `g j₀` leaves this explicit RHS. -/
def rhsCorrection (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (μ : Cube J) : Bool := f i₀ ^^ f (π j₀) ^^ μ j₀

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem correction_eq (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (g μ : Cube J) :
    (f i₀ ^^ g j₀ ^^ thirdQuery π f g μ j₀) = rhsCorrection π i₀ j₀ f μ := by
  change (f i₀ ^^ g j₀ ^^ (g j₀ ^^ (f (π j₀) ^^ μ j₀))) =
    (f i₀ ^^ f (π j₀) ^^ μ j₀)
  cases f i₀ <;> cases g j₀ <;> cases f (π j₀) <;> cases μ j₀ <;> rfl

/-- One sampled test becomes exactly one three-occurrence equation. -/
def equation (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr (canonicalInput j₀ g)
  third := .inr (canonicalInput j₀ (thirdQuery π f g μ))
  rhs := rhsCorrection π i₀ j₀ f μ

theorem xor_corrections (a b c u v w : Bool) :
    ((a ^^ b ^^ c) == (u ^^ v ^^ w)) =
      !((a ^^ u) ^^ (b ^^ v) ^^ (c ^^ w)) := by
  cases a <;> cases b <;> cases c <;> cases u <;> cases v <;> cases w <;> rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- Exact Boolean semantics, with the three stored bits read from one assignment.
There is no distinct-address assumption. -/
theorem equation_satisfied (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      !(foldedAnswer i₀ tableA f ^^ foldedAnswer j₀ tableB g ^^
        foldedAnswer j₀ tableB (thirdQuery π f g μ)) := by
  change ((tableA (canonicalInput i₀ f) ^^ tableB (canonicalInput j₀ g) ^^
      tableB (canonicalInput j₀ (thirdQuery π f g μ))) == rhsCorrection π i₀ j₀ f μ) = _
  rw [← correction_eq π i₀ j₀ f g μ]
  exact xor_corrections _ _ _ _ _ _

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem equation_satisfied_iff (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB) = true ↔
      (foldedAnswer i₀ tableA f ^^ foldedAnswer j₀ tableB g ^^
        foldedAnswer j₀ tableB (thirdQuery π f g μ)) = false := by
  rw [equation_satisfied]
  simp

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem equation_indicator (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    (if satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB)
      then (1 : ℝ) else 0) =
    (if foldedAnswer i₀ tableA f ^^ foldedAnswer j₀ tableB g ^^
      foldedAnswer j₀ tableB (thirdQuery π f g μ) then 0 else 1) := by
  rw [equation_satisfied]
  cases foldedAnswer i₀ tableA f ^^ foldedAnswer j₀ tableB g ^^
    foldedAnswer j₀ tableB (thirdQuery π f g μ) <;> rfl

/-- Repeated variable occurrences retain XOR multiplicity and cancel in pairs. -/
theorem satisfied_repeated_right {Name : Type} (e : Equation Name)
    (assignment : Name → Bool) (h : e.second = e.third) :
    satisfied e assignment = (assignment e.first == e.rhs) := by
  unfold satisfied
  rw [← h]
  cases assignment e.first <;> cases assignment e.second <;> cases e.rhs <;> rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem equation_repeated_right (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J)
    (h : canonicalInput j₀ g = canonicalInput j₀ (thirdQuery π f g μ)) :
    satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      (tableA (canonicalInput i₀ f) == rhsCorrection π i₀ j₀ f μ) := by
  apply satisfied_repeated_right
  exact congrArg Sum.inr h

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem restrict_thirdQuery (valid : J → Bool) (π : J → I)
    (f : Cube I) (g μ : Cube J) :
    restrictQuery valid (thirdQuery π f g μ) =
      thirdQuery (fun j : {j : J // valid j = true} => π j.val) f
        (restrictQuery valid g) (restrictQuery valid μ) := rfl

/-- Conditioned storage uses only satisfying-assignment coordinates, so identical
restricted canonical inputs are the same variable, even for distinct raw queries. -/
def conditionedEquation (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) :=
  equation (fun j => π j.val) i₀ j₀ f (restrictQuery valid g) (restrictQuery valid μ)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedEquation_rhs (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true}) (f : Cube I) (g μ : Cube J) :
    (conditionedEquation valid π i₀ j₀ f g μ).rhs =
      (f i₀ ^^ f (π j₀.val) ^^ μ j₀.val) := rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedEquation_satisfied (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedEquation valid π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      !(foldedAnswer i₀ tableA f ^^ conditionedFoldedAnswer valid j₀ tableB g ^^
        conditionedFoldedAnswer valid j₀ tableB (thirdQuery π f g μ)) := by
  unfold conditionedEquation
  rw [equation_satisfied]
  simp only [conditionedFoldedAnswer, restrict_thirdQuery]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedEquation_satisfied_iff (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedEquation valid π i₀ j₀ f g μ) (storedAssignment tableA tableB) = true ↔
      (foldedAnswer i₀ tableA f ^^ conditionedFoldedAnswer valid j₀ tableB g ^^
        conditionedFoldedAnswer valid j₀ tableB (thirdQuery π f g μ)) = false := by
  rw [conditionedEquation_satisfied]
  simp

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedEquation_indicator (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    (if satisfied (conditionedEquation valid π i₀ j₀ f g μ) (storedAssignment tableA tableB)
      then (1 : ℝ) else 0) =
    (if foldedAnswer i₀ tableA f ^^ conditionedFoldedAnswer valid j₀ tableB g ^^
      conditionedFoldedAnswer valid j₀ tableB (thirdQuery π f g μ) then 0 else 1) := by
  rw [conditionedEquation_satisfied]
  cases foldedAnswer i₀ tableA f ^^ conditionedFoldedAnswer valid j₀ tableB g ^^
    conditionedFoldedAnswer valid j₀ tableB (thirdQuery π f g μ) <;> rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedEquation_repeated_right (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J)
    (h : canonicalInput j₀ (restrictQuery valid g) =
      canonicalInput j₀ (restrictQuery valid (thirdQuery π f g μ))) :
    satisfied (conditionedEquation valid π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      (tableA (canonicalInput i₀ f) == (f i₀ ^^ f (π j₀.val) ^^ μ j₀.val)) := by
  apply satisfied_repeated_right
  exact congrArg Sum.inr h

noncomputable section

/-- Actual weighted acceptance of the emitted equation family. -/
def equationAcceptance (ε : ℝ) (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ *
    (𝔼 g, if satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB)
      then (1 : ℝ) else 0)

theorem equationAcceptance_eq (ε : ℝ) (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) :
    equationAcceptance ε π i₀ j₀ tableA tableB =
      testAcceptance ε π (foldedAnswer i₀ tableA) (foldedAnswer j₀ tableB) := by
  unfold equationAcceptance testAcceptance
  simp_rw [equation_indicator]

def conditionedEquationAcceptance (ε : ℝ) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ *
    (𝔼 g, if satisfied (conditionedEquation valid π i₀ j₀ f g μ)
      (storedAssignment tableA tableB) then (1 : ℝ) else 0)

theorem conditionedEquationAcceptance_eq (ε : ℝ) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) :
    conditionedEquationAcceptance ε valid π i₀ j₀ tableA tableB =
      testAcceptance ε π (foldedAnswer i₀ tableA)
        (conditionedFoldedAnswer valid j₀ tableB) := by
  unfold conditionedEquationAcceptance testAcceptance
  simp_rw [conditionedEquation_indicator]

end

end MaxCutGames.Foundations.Hastad.FoldedEquation

/-!
Actual equations for clause contexts having no valid local assignment. The
right answer is the constant false bit, represented by two occurrences of one
dummy variable. Those occurrences cancel for every assignment. The remaining
left answer is folded, so its uniform bias is exactly zero.
-/

namespace MaxCutGames.Foundations.Hastad

open MaxCutGames.Reduction.CloneGap
open scoped BigOperators

/-- Rename the three occurrences without merging or dropping any occurrence. -/
def mapEquation {Name Name' : Type} (rename : Name → Name')
    (e : Equation Name) : Equation Name' where
  first := rename e.first
  second := rename e.second
  third := rename e.third
  rhs := e.rhs

theorem satisfied_mapEquation {Name Name' : Type} (rename : Name → Name')
    (e : Equation Name) (assignment : Name' → Bool) :
    satisfied (mapEquation rename e) assignment = satisfied e (assignment ∘ rename) := rfl

namespace EmptyContext

variable {I : Type} [Fintype I] [DecidableEq I]

/-- A left half-table address or the one dummy address. -/
abbrev Address (i₀ : I) := HalfCube i₀ ⊕ Unit

def storedAssignment {i₀ : I} (table : HalfCube i₀ → Bool) (dummy : Bool) :
    Address i₀ → Bool := Sum.elim table (fun _ => dummy)

/-- The dummy appears twice. Its assigned bit cancels in the equation. -/
def equation (i₀ : I) (f : Cube I) : Equation (Address i₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr ()
  third := .inr ()
  rhs := f i₀

omit [Fintype I] [DecidableEq I] in
@[simp] theorem equation_second_eq_third (i₀ : I) (f : Cube I) :
    (equation i₀ f).second = (equation i₀ f).third := rfl

omit [Fintype I] [DecidableEq I] in
/-- Exact semantics for every assignment, including an arbitrary dummy bit. -/
theorem equation_satisfied (i₀ : I) (assignment : Address i₀ → Bool) (f : Cube I) :
    satisfied (equation i₀ f) assignment =
      !(foldedAnswer i₀ (fun h => assignment (.inl h)) f) := by
  rw [FoldedEquation.satisfied_repeated_right (equation i₀ f) assignment rfl]
  change (assignment (.inl (canonicalInput i₀ f)) == f i₀) =
    !(assignment (.inl (canonicalInput i₀ f)) ^^ f i₀)
  cases assignment (.inl (canonicalInput i₀ f)) <;> cases f i₀ <;> rfl

omit [Fintype I] [DecidableEq I] in
theorem equation_storedAssignment_satisfied (i₀ : I) (table : HalfCube i₀ → Bool)
    (dummy : Bool) (f : Cube I) :
    satisfied (equation i₀ f) (storedAssignment table dummy) =
      !(foldedAnswer i₀ table f) := equation_satisfied i₀ _ f

omit [Fintype I] [DecidableEq I] in
/-- Flipping the query preserves all three addresses and reverses the RHS. -/
theorem equation_flip_first (i₀ : I) (f : Cube I) :
    (equation i₀ (cubeFlip f)).first = (equation i₀ f).first := by
  change Sum.inl (canonicalInput i₀ (cubeFlip f)) = Sum.inl (canonicalInput i₀ f)
  rw [canonicalInput_flip]

omit [Fintype I] [DecidableEq I] in
theorem equation_flip_rhs (i₀ : I) (f : Cube I) :
    (equation i₀ (cubeFlip f)).rhs = !(equation i₀ f).rhs := rfl

omit [Fintype I] [DecidableEq I] in
theorem equation_satisfied_flip (i₀ : I) (assignment : Address i₀ → Bool)
    (f : Cube I) :
    satisfied (equation i₀ (cubeFlip f)) assignment =
      !(satisfied (equation i₀ f) assignment) := by
  rw [equation_satisfied, foldedAnswer_flip, equation_satisfied]

/-- The two opposite queries give an explicit balanced list of equations. -/
def pairedEquations (i₀ : I) (f : Cube I) : List (Equation (Address i₀)) :=
  [equation i₀ f, equation i₀ (cubeFlip f)]

omit [Fintype I] [DecidableEq I] in
@[simp] theorem pairedEquations_length (i₀ : I) (f : Cube I) :
    (pairedEquations i₀ f).length = 2 := rfl

omit [Fintype I] [DecidableEq I] in
theorem pairedEquations_ne_nil (i₀ : I) (f : Cube I) :
    pairedEquations i₀ f ≠ [] := by simp [pairedEquations]

omit [Fintype I] [DecidableEq I] in
/-- Exactly one actual equation in the pair accepts every fixed proof. -/
theorem pairedEquations_acceptedCount (i₀ : I) (assignment : Address i₀ → Bool)
    (f : Cube I) :
    (pairedEquations i₀ f).countP (fun e => satisfied e assignment) = 1 := by
  simp only [pairedEquations, List.countP_cons, List.countP_nil, equation_satisfied_flip]
  cases satisfied (equation i₀ f) assignment <;> rfl

omit [Fintype I] [DecidableEq I] in
theorem pairedEquations_failureCount (i₀ : I) (assignment : Address i₀ → Bool)
    (f : Cube I) :
    (pairedEquations i₀ f).countP (fun e => !(satisfied e assignment)) = 1 := by
  simp only [pairedEquations, List.countP_cons, List.countP_nil, equation_satisfied_flip]
  cases satisfied (equation i₀ f) assignment <;> rfl

noncomputable section

def equationAcceptance (i₀ : I) (assignment : Address i₀ → Bool) : ℝ :=
  𝔼 f : Cube I, if satisfied (equation i₀ f) assignment then (1 : ℝ) else 0

def equationBias (i₀ : I) (assignment : Address i₀ → Bool) : ℝ :=
  𝔼 f : Cube I, if satisfied (equation i₀ f) assignment then (1 : ℝ) else -1

theorem foldedMean_eq_zero (i₀ : I) (table : HalfCube i₀ → Bool) :
    (𝔼 f : Cube I, bitSign (foldedAnswer i₀ table f)) = 0 := by
  simpa [coefficient, walsh, bitSign] using foldedAnswer_zero_coefficient i₀ table

omit [Fintype I] [DecidableEq I] in
theorem equation_indicator (i₀ : I) (assignment : Address i₀ → Bool) (f : Cube I) :
    (if satisfied (equation i₀ f) assignment then (1 : ℝ) else 0) =
      (1 + bitSign (foldedAnswer i₀ (fun h => assignment (.inl h)) f)) / 2 := by
  rw [equation_satisfied]
  cases foldedAnswer i₀ (fun h => assignment (.inl h)) f <;> norm_num [bitSign]

/-- Uniform queries accept with probability exactly one half. No right
folding anchor, valid right assignment, or placeholder response is assumed. -/
theorem equationAcceptance_eq_half (i₀ : I) (assignment : Address i₀ → Bool) :
    equationAcceptance i₀ assignment = 1 / 2 := by
  unfold equationAcceptance
  simp_rw [equation_indicator, div_eq_mul_inv, ← Finset.expect_mul,
    Finset.expect_add_distrib, Fintype.expect_const, foldedMean_eq_zero]
  norm_num

/-- The signed acceptance of the actual emitted equations has zero bias. -/
theorem equationBias_eq_zero (i₀ : I) (assignment : Address i₀ → Bool) :
    equationBias i₀ assignment = 0 := by
  unfold equationBias
  have hi (f : Cube I) :
      (if satisfied (equation i₀ f) assignment then (1 : ℝ) else -1) =
        bitSign (foldedAnswer i₀ (fun h => assignment (.inl h)) f) := by
    rw [equation_satisfied]
    cases foldedAnswer i₀ (fun h => assignment (.inl h)) f <;> norm_num [bitSign]
  simp_rw [hi]
  exact foldedMean_eq_zero i₀ _

theorem mapped_equationAcceptance_eq_half {Name : Type} (i₀ : I)
    (rename : Address i₀ → Name) (assignment : Name → Bool) :
    (𝔼 f : Cube I, if satisfied (mapEquation rename (equation i₀ f)) assignment
      then (1 : ℝ) else 0) = 1 / 2 := by
  simp only [satisfied_mapEquation]
  exact equationAcceptance_eq_half i₀ (assignment ∘ rename)

end
end EmptyContext
end MaxCutGames.Foundations.Hastad

end OAI
