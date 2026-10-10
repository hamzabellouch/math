import OAI.Combinatorics.GraphThreshold.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

@[simp] theorem expectation_const (μ : FiniteLaw Ω) (c : ℝ) :
    μ.expectation (fun _ => c) = c := by
  rw [expectation, ← Finset.sum_mul, μ.total, one_mul]

theorem expectation_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun ω => f ω + g ω) = μ.expectation f + μ.expectation g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun ω => f ω - g ω) = μ.expectation f - μ.expectation g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_smul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.expectation (fun ω => c * f ω) = c * μ.expectation f := by
  simp [expectation, Finset.mul_sum, mul_left_comm]

theorem expectation_sum {ι : Type*} [Fintype ι] (μ : FiniteLaw Ω) (f : ι → Ω → ℝ) :
    μ.expectation (fun ω => ∑ i, f i ω) = ∑ i, μ.expectation (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem expectation_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ μ.expectation f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω)

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

theorem prob_eq_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob P = μ.expectation (fun ω => if P ω then 1 else 0) := by
  classical
  simp [prob, expectation, mul_ite]

@[simp] theorem prob_true (μ : FiniteLaw Ω) : μ.prob (fun _ => True) = 1 := by
  simp [prob, μ.total]

@[simp] theorem prob_false (μ : FiniteLaw Ω) : μ.prob (fun _ => False) = 0 := by
  simp [prob]

theorem prob_nonneg (μ : FiniteLaw Ω) (P : Ω → Prop) : 0 ≤ μ.prob P := by
  classical
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [μ.nonneg]

theorem prob_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop} (hPQ : ∀ ω, P ω → Q ω) :
    μ.prob P ≤ μ.prob Q := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω
  · simp [hp, hPQ ω hp]
  · by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg ω]

theorem prob_le_one (μ : FiniteLaw Ω) (P : Ω → Prop) : μ.prob P ≤ 1 := by
  simpa using μ.prob_mono (Q := fun _ => True) (fun _ _ => trivial)

theorem prob_compl (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob (fun ω => ¬ P ω) = 1 - μ.prob P := by
  classical
  have h : μ.prob P + μ.prob (fun ω => ¬ P ω) = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib, ← μ.total]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hp : P ω <;> simp [hp]
  linarith

theorem prob_union_le (μ : FiniteLaw Ω) (P Q : Ω → Prop) :
    μ.prob (fun ω => P ω ∨ Q ω) ≤ μ.prob P + μ.prob Q := by
  classical
  rw [prob, prob, prob, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg]

theorem prob_le_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hP : ∀ ω, P ω → 1 ≤ f ω) : μ.prob P ≤ μ.expectation f := by
  classical
  rw [prob_eq_expectation]
  apply μ.expectation_mono
  intro ω
  by_cases hp : P ω
  · simpa [hp] using hP ω hp
  · simpa [hp] using hf ω

theorem prob_ge_le_expectation_div (μ : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) {t : ℝ} (ht : 0 < t) :
    μ.prob (fun ω => t ≤ f ω) ≤ μ.expectation f / t := by
  have h := μ.prob_le_expectation (fun ω => t ≤ f ω) (fun ω => t⁻¹ * f ω)
    (fun ω => mul_nonneg (inv_nonneg.mpr ht.le) (hf ω))
    (fun ω hω => by simpa [ht.ne'] using mul_le_mul_of_nonneg_left hω (inv_nonneg.mpr ht.le))
  rw [expectation_smul] at h
  simpa [div_eq_mul_inv, mul_comm] using h

def prod (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) : FiniteLaw (Ω × Γ) where
  weight ω := μ.weight ω.1 * ν.weight ω.2
  nonneg ω := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ν.total, mul_one, μ.total]

@[simp] theorem prod_weight (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (ω : Ω) (γ : Γ) :
    (μ.prod ν).weight (ω, γ) = μ.weight ω * ν.weight γ := rfl

theorem expectation_prod (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (f : Ω × Γ → ℝ) :
    (μ.prod ν).expectation f = μ.expectation (fun ω => ν.expectation (fun γ => f (ω, γ))) := by
  simp [expectation, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem prod_isPositive (μ : FiniteLaw Ω) (ν : FiniteLaw Γ)
    (hμ : μ.IsPositive) (hν : ν.IsPositive) : (μ.prod ν).IsPositive :=
  fun ω => mul_pos (hμ ω.1) (hν ω.2)

def pi {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (μ : ∀ i, FiniteLaw (A i)) : FiniteLaw (∀ i, A i) := by
  classical
  exact {
    weight := fun ω => ∏ i, (μ i).weight (ω i)
    nonneg := fun ω => Finset.prod_nonneg fun i _ => (μ i).nonneg (ω i)
    total := by
      rw [← Fintype.prod_sum (fun i a => (μ i).weight a)]
      simp_rw [(μ _).total]
      simp }

@[simp] theorem pi_weight {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (μ : ∀ i, FiniteLaw (A i)) (ω : ∀ i, A i) :
    (pi μ).weight ω = ∏ i, (μ i).weight (ω i) := rfl

def iid (μ : FiniteLaw Ω) (n : ℕ) : FiniteLaw (Fin n → Ω) := pi (fun _ : Fin n => μ)

@[simp] theorem iid_weight (μ : FiniteLaw Ω) (n : ℕ) (ω : Fin n → Ω) :
    (iid μ n).weight ω = ∏ i, μ.weight (ω i) := rfl

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [hN]

theorem uniform_isPositive (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    (uniform Ω).IsPositive := fun _ => inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

theorem uniform_prob (Ω : Type*) [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    (uniform Ω).prob P = ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω := by
  simp [prob, uniform, ← Finset.sum_filter, div_eq_mul_inv]

end FiniteLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

def finsetBoolEquiv : Finset X ≃ (X → Bool) where
  toFun W x := decide (x ∈ W)
  invFun b := Finset.univ.filter fun x => b x = true
  left_inv W := by ext x; simp
  right_inv b := by
    funext x
    cases hb : b x <;> simp [hb]

theorem sum_finset_product (f : X → Bool → ℝ) :
    (∑ W : Finset X, ∏ x, f x (decide (x ∈ W))) =
      ∏ x, (f x true + f x false) := by
  calc
    (∑ W : Finset X, ∏ x, f x (decide (x ∈ W))) =
        ∑ b : X → Bool, ∏ x, f x (b x) :=
      (finsetBoolEquiv (X := X)).sum_comp (fun b => ∏ x, f x (b x))
    _ = _ := by rw [← Fintype.prod_sum f]; simp only [Fintype.sum_bool]

theorem bernoulliExpectation_product (p : ℝ) (f : X → Bool → ℝ) :
    bernoulliExpectation p (fun W => ∏ x, f x (decide (x ∈ W))) =
      ∏ x, (p * f x true + (1 - p) * f x false) := by
  unfold bernoulliExpectation bernoulliWeight
  simp_rw [← Finset.prod_mul_distrib]
  simpa using sum_finset_product (fun x b => (if b then p else 1 - p) * f x b)

theorem bernoulliWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset X) :
    0 ≤ bernoulliWeight p W := by
  apply Finset.prod_nonneg
  intro x _
  split_ifs <;> linarith

theorem bernoulliWeight_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (W : Finset X) :
    0 < bernoulliWeight p W := by
  apply Finset.prod_pos
  intro x _
  split_ifs <;> linarith

theorem bernoulliWeight_sum (p : ℝ) : ∑ W : Finset X, bernoulliWeight p W = 1 := by
  have hp : p + (1 - p) = 1 := by ring
  simpa [bernoulliExpectation, hp] using
    bernoulliExpectation_product p (fun (_ : X) (_ : Bool) => 1)

def bernoulliLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw (Finset X) where
  weight := bernoulliWeight p
  nonneg := bernoulliWeight_nonneg hp0 hp1
  total := bernoulliWeight_sum p

@[simp] theorem bernoulliLaw_weight (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset X) :
    (bernoulliLaw p hp0 hp1).weight W = bernoulliWeight p W := rfl

@[simp] theorem bernoulliLaw_expectation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Finset X → ℝ) :
    (bernoulliLaw p hp0 hp1).expectation f = bernoulliExpectation p f := rfl

@[simp] theorem bernoulliLaw_prob (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : Finset X → Prop) : (bernoulliLaw p hp0 hp1).prob P = bernoulliProbability p P := rfl

theorem bernoulliProbability_eq_expectation (p : ℝ) (P : Finset X → Prop) :
    bernoulliProbability p P = bernoulliExpectation p (fun W => if P W then 1 else 0) := by
  classical
  simp [bernoulliProbability, bernoulliExpectation, mul_ite]

theorem subset_indicator_product (A W : Finset X) :
    (if A ⊆ W then (1 : ℝ) else 0) =
      ∏ x, (if x ∈ A then (if x ∈ W then (1 : ℝ) else 0) else 1) := by
  rw [Fintype.prod_ite_mem, Finset.prod_boole]
  rfl

theorem bernoulliProbability_subset (p : ℝ) (A : Finset X) :
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

end LeanBlast.SecondKahnKalai

end

end OAI
