import OAI.Combinatorics.DiscreteConvexity.Basic
import OAI.Combinatorics.DiscreteConvexity.FiniteProbability
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Bernoulli product laws and Boolean cubes

The algebraic identities hold for every real parameter. Nonnegative normalized
laws additionally require a parameter in the closed unit interval.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandDiscreteConvexity

/-- The mass of a Bernoulli bit. -/
def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

@[simp] theorem bitWeight_true (p : ℝ) : bitWeight p true = p := rfl
@[simp] theorem bitWeight_false (p : ℝ) : bitWeight p false = 1 - p := rfl

theorem bitWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bitWeight p b := by
  cases b
  · exact sub_nonneg.mpr hp1
  · exact hp0

def bitLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw Bool where
  weight := bitWeight p
  nonneg := bitWeight_nonneg hp0 hp1
  total := by simp [bitWeight]

@[simp] theorem bitLaw_weight (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    (bitLaw p hp0 hp1).weight b = bitWeight p b := rfl

@[simp] theorem bitLaw_prob_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bitLaw p hp0 hp1).prob (fun b => b = true) = p := by
  simp [FiniteLaw.prob, bitLaw, bitWeight]

@[simp] theorem bitLaw_prob_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bitLaw p hp0 hp1).prob (fun b => b = false) = 1 - p := by
  simp [FiniteLaw.prob, bitLaw, bitWeight]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Product mass on the Boolean cube, including signed parameters. -/
def cubeWeight (p : ℝ) (x : α → Bool) : ℝ := ∏ i, bitWeight p (x i)

def cubeExpectation (p : ℝ) (f : (α → Bool) → ℝ) : ℝ :=
  ∑ x, cubeWeight p x * f x

def bernoulliWeight (p : ℝ) (s : Finset α) : ℝ :=
  ∏ i, if i ∈ s then p else 1 - p

def bernoulliExpectation (p : ℝ) (f : Finset α → ℝ) : ℝ :=
  ∑ s, bernoulliWeight p s * f s

def bernoulliProbability (p : ℝ) (P : Finset α → Prop) : ℝ :=
  ∑ s, if P s then bernoulliWeight p s else 0

def finsetBoolEquiv : Finset α ≃ (α → Bool) where
  toFun W x := decide (x ∈ W)
  invFun b := Finset.univ.filter fun x => b x = true
  left_inv W := by ext x; simp
  right_inv b := by
    funext x
    cases hb : b x <;> simp [hb]

theorem sum_finset_product (f : α → Bool → ℝ) :
    (∑ W : Finset α, ∏ x, f x (decide (x ∈ W))) =
      ∏ x, (f x true + f x false) := by
  calc
    (∑ W : Finset α, ∏ x, f x (decide (x ∈ W))) =
        ∑ b : α → Bool, ∏ x, f x (b x) :=
      (finsetBoolEquiv (α := α)).sum_comp (fun b => ∏ x, f x (b x))
    _ = _ := by rw [← Fintype.prod_sum f]; simp only [Fintype.sum_bool]

theorem bernoulliExpectation_product (p : ℝ) (f : α → Bool → ℝ) :
    bernoulliExpectation p (fun W => ∏ x, f x (decide (x ∈ W))) =
      ∏ x, (p * f x true + (1 - p) * f x false) := by
  unfold bernoulliExpectation bernoulliWeight
  simp_rw [← Finset.prod_mul_distrib]
  simpa using sum_finset_product (fun x b => (if b then p else 1 - p) * f x b)

theorem bernoulliWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset α) :
    0 ≤ bernoulliWeight p W := by
  apply Finset.prod_nonneg
  intro x _
  split_ifs <;> linarith

theorem bernoulliWeight_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (W : Finset α) :
    0 < bernoulliWeight p W := by
  apply Finset.prod_pos
  intro x _
  split_ifs <;> linarith

theorem bernoulliWeight_sum (p : ℝ) : ∑ W : Finset α, bernoulliWeight p W = 1 := by
  have hp : p + (1 - p) = 1 := by ring
  simpa [bernoulliExpectation, hp] using
    bernoulliExpectation_product p (fun (_ : α) (_ : Bool) => 1)

def bernoulliLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw (Finset α) where
  weight := bernoulliWeight p
  nonneg := bernoulliWeight_nonneg hp0 hp1
  total := bernoulliWeight_sum p

@[simp] theorem bernoulliLaw_weight (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset α) :
    (bernoulliLaw p hp0 hp1).weight W = bernoulliWeight p W := rfl

@[simp] theorem bernoulliLaw_expectation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Finset α → ℝ) :
    (bernoulliLaw p hp0 hp1).expectation f = bernoulliExpectation p f := rfl

@[simp] theorem bernoulliLaw_prob (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : Finset α → Prop) : (bernoulliLaw p hp0 hp1).prob P = bernoulliProbability p P := rfl

theorem bernoulliProbability_eq_expectation (p : ℝ) (P : Finset α → Prop) :
    bernoulliProbability p P = bernoulliExpectation p (fun W => if P W then 1 else 0) := by
  classical
  simp [bernoulliProbability, bernoulliExpectation, mul_ite]

theorem subset_indicator_product (A W : Finset α) :
    (if A ⊆ W then (1 : ℝ) else 0) =
      ∏ x, (if x ∈ A then (if x ∈ W then (1 : ℝ) else 0) else 1) := by
  rw [Fintype.prod_ite_mem, Finset.prod_boole]
  rfl

theorem bernoulliProbability_subset (p : ℝ) (A : Finset α) :
    bernoulliProbability p (fun W => A ⊆ W) = p ^ A.card := by
  trans bernoulliExpectation p (fun W =>
    ∏ x, (if x ∈ A then (if x ∈ W then (1 : ℝ) else 0) else 1))
  · unfold bernoulliProbability bernoulliExpectation
    apply Finset.sum_congr rfl
    intro W _
    dsimp only
    by_cases hs : A ⊆ W
    · have hh := (subset_indicator_product A W).symm
      simp only [ite_eq_left hs] at hh
      rw [hh]
      simp [hs]
    · have hh := (subset_indicator_product A W).symm
      simp only [ite_eq_right hs] at hh
      rw [hh]
      simp [hs]
  calc
    bernoulliExpectation p (fun W =>
        ∏ x, (if x ∈ A then (if x ∈ W then (1 : ℝ) else 0) else 1)) =
        ∏ x, (p * (if x ∈ A then (1 : ℝ) else 1) +
          (1 - p) * (if x ∈ A then (0 : ℝ) else 1)) := by
      simpa only [decide_eq_true_eq, Bool.true_eq, ite_true, Bool.false_eq_true, ite_false] using
        bernoulliExpectation_product p
          (fun x b => if x ∈ A then (if b then (1 : ℝ) else 0) else 1)
    _ = ∏ x, (if x ∈ A then p else 1) := by
      apply Finset.prod_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [hx]
    _ = p ^ A.card := by rw [Fintype.prod_ite_mem]; simp

theorem bernoulliWeight_eq_mass (p : ℝ) (s : Finset α) :
    bernoulliWeight p s = bernoulliMass p s := by
  simp only [bernoulliWeight, bernoulliMass, Finset.prod_ite,
    Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.filter_notMem_eq_sdiff, Finset.prod_const]

@[simp] theorem cubeSet_finsetBoolEquiv (s : Finset α) :
    cubeSet (finsetBoolEquiv s) = s := cubeSet_decide s

@[simp] theorem cubeWeight_finsetBoolEquiv (p : ℝ) (s : Finset α) :
    cubeWeight p (finsetBoolEquiv s) = bernoulliWeight p s := by
  simp [cubeWeight, bitWeight, finsetBoolEquiv, bernoulliWeight]

omit [DecidableEq α] in
theorem cubeWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : α → Bool) :
    0 ≤ cubeWeight p x :=
  Finset.prod_nonneg (fun i _ => bitWeight_nonneg hp0 hp1 (x i))

theorem cubeWeight_sum (p : ℝ) : ∑ x : α → Bool, cubeWeight p x = 1 := by
  rw [← (finsetBoolEquiv (α := α)).sum_comp (cubeWeight p)]
  simpa only [cubeWeight_finsetBoolEquiv] using bernoulliWeight_sum (α := α) p

theorem cubeExpectation_eq_bernoulliExpectation (p : ℝ) (f : (α → Bool) → ℝ) :
    cubeExpectation p f = bernoulliExpectation p (fun s => f (finsetBoolEquiv s)) := by
  unfold cubeExpectation bernoulliExpectation
  rw [← (finsetBoolEquiv (α := α)).sum_comp (fun x => cubeWeight p x * f x)]
  simp only [cubeWeight_finsetBoolEquiv]

theorem cubeExpectation_product (p : ℝ) (f : α → Bool → ℝ) :
    cubeExpectation p (fun x => ∏ i, f i (x i)) =
      ∏ i, (p * f i true + (1 - p) * f i false) := by
  rw [cubeExpectation_eq_bernoulliExpectation]
  exact bernoulliExpectation_product p f

theorem cubeExpectation_familyIndicator (p : ℝ) (D : Family α) :
    cubeExpectation p (familyIndicator D) = familyMeasure p D := by
  rw [cubeExpectation_eq_bernoulliExpectation]
  simp only [bernoulliExpectation, familyIndicator, cubeSet_finsetBoolEquiv,
    mul_ite, mul_one, mul_zero, bernoulliWeight_eq_mass]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rfl

theorem bernoulliLaw_prob_subset (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Finset α) :
    (bernoulliLaw p hp0 hp1).prob (fun s => A ⊆ s) = p ^ A.card :=
  bernoulliProbability_subset p A

theorem bernoulliLaw_prob_mem (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a : α) :
    (bernoulliLaw p hp0 hp1).prob (fun s => a ∈ s) = p := by
  simpa using bernoulliLaw_prob_subset p hp0 hp1 ({a} : Finset α)

theorem disjoint_indicator_product (A W : Finset α) :
    (if Disjoint W A then (1 : ℝ) else 0) =
      ∏ x, (if x ∈ A then (if x ∈ W then (0 : ℝ) else 1) else 1) := by
  simp only [Finset.disjoint_right]
  rw [Fintype.prod_ite_mem]
  have h (x : α) : (if x ∈ W then (0 : ℝ) else 1) =
      if x ∉ W then 1 else 0 := by
    by_cases hx : x ∈ W <;> simp [hx]
  simp_rw [h]
  rw [Finset.prod_boole]
  by_cases hexp : ∀ i ∈ A, i ∉ W
  · have himp : ∀ ⦃i : α⦄, i ∈ A → i ∉ W := by
      intro i hi
      exact hexp i hi
    simp only [ite_eq_left himp]
  · have himp : ¬ (∀ ⦃i : α⦄, i ∈ A → i ∉ W) := by
      intro hi
      exact hexp (fun i hai => hi hai)
    simp only [ite_eq_right himp]

theorem bernoulliProbability_disjoint (p : ℝ) (A : Finset α) :
    bernoulliProbability p (fun W => Disjoint W A) = (1 - p) ^ A.card := by
  rw [bernoulliProbability_eq_expectation]
  trans bernoulliExpectation p (fun W =>
    ∏ x, (if x ∈ A then (if x ∈ W then (0 : ℝ) else 1) else 1))
  · congr 1
    funext W
    by_cases h : Disjoint W A <;>
      simpa [h] using disjoint_indicator_product A W
  calc
    bernoulliExpectation p (fun W =>
        ∏ x, (if x ∈ A then (if x ∈ W then (0 : ℝ) else 1) else 1)) =
        ∏ x, (p * (if x ∈ A then (0 : ℝ) else 1) +
          (1 - p) * (if x ∈ A then (1 : ℝ) else 1)) := by
      simpa only [decide_eq_true_eq, Bool.true_eq, ite_true, Bool.false_eq_true, ite_false] using
        bernoulliExpectation_product p
          (fun x b => if x ∈ A then (if b then (0 : ℝ) else 1) else 1)
    _ = ∏ x, (if x ∈ A then 1 - p else 1) := by
      apply Finset.prod_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [hx]
    _ = (1 - p) ^ A.card := by rw [Fintype.prod_ite_mem]; simp

theorem bernoulliLaw_prob_disjoint (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Finset α) :
    (bernoulliLaw p hp0 hp1).prob (fun W => Disjoint W A) = (1 - p) ^ A.card :=
  bernoulliProbability_disjoint p A

theorem bernoulliLaw_expect_sum_mem (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : α → ℝ) :
    (bernoulliLaw p hp0 hp1).expectation (fun W => ∑ x ∈ W, f x) = p * ∑ x, f x := by
  classical
  let μ : FiniteLaw (Finset α) := bernoulliLaw p hp0 hp1
  have hsum (W : Finset α) :
      (∑ x ∈ W, f x) = ∑ x, if x ∈ W then f x else 0 := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hx (x : α) :
      μ.expectation (fun W => if x ∈ W then f x else 0) = p * f x := by
    calc
      _ = μ.expectation (fun W => f x * (if x ∈ W then 1 else 0)) := by
        congr 1
        funext W
        by_cases h : x ∈ W <;> simp [h]
      _ = f x * μ.prob (fun W => x ∈ W) := by
        rw [FiniteLaw.expectation_smul]
        apply congrArg (fun z : ℝ => f x * z)
        rw [FiniteLaw.prob_eq_expectation]
        apply congrArg μ.expectation
        funext W
        by_cases h : x ∈ W <;> simp [h]
      _ = p * f x := by
        rw [show μ.prob (fun W => x ∈ W) = p from bernoulliLaw_prob_mem p hp0 hp1 x]
        exact mul_comm _ _
  change μ.expectation (fun W => ∑ x ∈ W, f x) = p * ∑ x, f x
  simp_rw [hsum]
  rw [FiniteLaw.expectation_sum]
  simp_rw [hx]
  simpa only [Finset.mem_univ, ite_true] using (Finset.mul_sum Finset.univ f p).symm

end TalagrandDiscreteConvexity

end

end OAI
