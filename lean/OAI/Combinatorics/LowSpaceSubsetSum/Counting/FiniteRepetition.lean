import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FiniteSamplerCoupling
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Amplification
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-! # Independent complete rounds and the fixed finite repetition schedule

The product law retains both actual outcomes, including sampler exhaustion.
Repetition draws fresh complete rounds and accepts if any round accepts.
-/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace FiniteLaw

variable {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]

/-- Independent actual outcomes. A failure value in either coordinate does
not prevent the other coordinate from being drawn. -/
def prod (μ : FiniteLaw Ω) (ν : FiniteLaw Ψ) : FiniteLaw (Ω × Ψ) where
  mass x := μ.mass x.1 * ν.mass x.2
  nonneg x := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.total, mul_one]
    exact μ.total

theorem prod_first_probability (μ : FiniteLaw Ω) (ν : FiniteLaw Ψ) (P : Ω → Prop) :
    (μ.prod ν).probability (fun x => P x.1) = μ.probability P := by
  classical
  simp only [probability, prod, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x
  · simp only [hx, ↓reduceIte, ← Finset.mul_sum, ν.total, mul_one]
  · simp [hx]

theorem prod_second_probability (μ : FiniteLaw Ω) (ν : FiniteLaw Ψ) (P : Ψ → Prop) :
    (μ.prod ν).probability (fun x => P x.2) = ν.probability P := by
  classical
  simp only [probability, prod, Fintype.sum_prod_type]
  have hpoint (x : Ω) :
      (∑ y, if P y then μ.mass x * ν.mass y else 0) =
        μ.mass x * ∑ y, if P y then ν.mass y else 0 := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  simp_rw [hpoint]
  rw [← Finset.sum_mul, μ.total, one_mul]

theorem prod_or_ge_left (μ : FiniteLaw Ω) (ν : FiniteLaw Ψ)
    (P : Ω → Prop) (Q : Ψ → Prop) :
    μ.probability P ≤ (μ.prod ν).probability (fun x => P x.1 ∨ Q x.2) := by
  rw [← prod_first_probability μ ν P]
  exact probability_mono _ (fun _ h => Or.inl h)

theorem prod_or_ge_right (μ : FiniteLaw Ω) (ν : FiniteLaw Ψ)
    (P : Ω → Prop) (Q : Ψ → Prop) :
    ν.probability Q ≤ (μ.prod ν).probability (fun x => P x.1 ∨ Q x.2) := by
  rw [← prod_second_probability μ ν Q]
  exact probability_mono _ (fun _ h => Or.inr h)

/-- Fresh independent draws, allowing a different finite law at each index. -/
def pi {I : Type*} [Fintype I] [DecidableEq I] (A : I → Type*) [∀ i, Fintype (A i)]
    (μ : ∀ i, FiniteLaw (A i)) : FiniteLaw (∀ i, A i) where
  mass x := ∏ i, (μ i).mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (μ i).nonneg (x i))
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp only [(μ _).total, Finset.prod_const_one]

theorem pi_forall_probability {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (P : ∀ i, A i → Prop) :
    (pi A μ).probability (fun x => ∀ i, P i (x i)) =
      ∏ i, (μ i).probability (P i) := by
  classical
  simp only [probability, pi]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hp := (Fintype.prod_ite_zero (p := fun i => P i (x i))
    (f := fun i => (μ i).mass (x i))).symm
  by_cases h : ∀ i, P i (x i)
  · simpa only [h, ↓reduceIte] using hp
  · simpa only [h, ↓reduceIte] using hp

def iid (μ : FiniteLaw Ω) (k : ℕ) : FiniteLaw (Fin k → Ω) :=
  pi (fun _ : Fin k => Ω) (fun _ => μ)

theorem iid_forall_probability (μ : FiniteLaw Ω) (k : ℕ) (P : Ω → Prop) :
    (μ.iid k).probability (fun x => ∀ i, P (x i)) = (μ.probability P) ^ k := by
  rw [iid, pi_forall_probability]
  simp

theorem iid_exists_probability (μ : FiniteLaw Ω) (k : ℕ) (P : Ω → Prop) :
    (μ.iid k).probability (fun x => ∃ i, P (x i)) =
      1 - (1 - μ.probability P) ^ k := by
  have he : (fun x : Fin k → Ω => ∃ i, P (x i)) =
      (fun x => ¬∀ i, ¬P (x i)) := by
    funext x
    exact propext (by simp)
  rw [he, probability_compl,
    iid_forall_probability μ k (fun x => ¬P x), probability_compl]

end FiniteLaw

/-- The executable finite OR of complete trial outcomes. -/
def repeatAccept {Ω : Type*} {k : ℕ} (test : Ω → Bool) (draws : Fin k → Ω) : Bool :=
  (List.finRange k).any (fun i => test (draws i))

theorem repeatAccept_eq_true {Ω : Type*} {k : ℕ} (test : Ω → Bool)
    (draws : Fin k → Ω) :
    repeatAccept test draws = true ↔ ∃ i, test (draws i) = true := by
  simp [repeatAccept]

theorem repeatAccept_sound {Ω : Type*} {k : ℕ} (test : Ω → Bool)
    (P : Prop) (hsound : ∀ x, test x = true → P) (draws : Fin k → Ω)
    (h : repeatAccept test draws = true) : P := by
  obtain ⟨i, hi⟩ := (repeatAccept_eq_true test draws).mp h
  exact hsound (draws i) hi

theorem repetition_acceptance_probability {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (test : Ω → Bool) {u : ℕ} (hu : 2 ≤ u)
    (hp : 1 / (u : ℝ) ^ 110 ≤ μ.probability (fun x => test x = true)) :
    (2 / 3 : ℝ) < (μ.iid (u ^ 120)).probability
      (fun draws => repeatAccept test draws = true) := by
  simp_rw [repeatAccept_eq_true]
  rw [FiniteLaw.iid_exists_probability μ (u ^ 120) (fun x => test x = true)]
  have hq0 := sub_nonneg.mpr (μ.probability_le_one (fun x => test x = true))
  have hq : 1 - μ.probability (fun x => test x = true) ≤ 1 - 1 / (u : ℝ) ^ 110 := by
    linarith
  have hsmall := amplification_bound hu hq0 hq
  linarith

/-- Exhaustion is a rejecting actual outcome, without conditioning the law. -/
def optionAccept {α : Type*} (test : α → Bool) : Option α → Bool
  | none => false
  | some x => test x

theorem optionAccept_eq_true {α : Type*} (test : α → Bool) (o : Option α) :
    optionAccept test o = true ↔ ∃ x, o = some x ∧ test x = true := by
  cases o <;> simp [optionAccept]

theorem bounded_repetition_acceptance_probability {α : Type*} [Fintype α]
    (S : SamplerCoupling α) (test : α → Bool) {u : ℕ} (hu : 2 ≤ u)
    (hp : 1 / (u : ℝ) ^ 110 ≤ S.boundedLaw.probability
      (fun o => ∃ x, o = some x ∧ test x = true)) :
    (2 / 3 : ℝ) < (S.boundedLaw.iid (u ^ 120)).probability
      (fun draws => repeatAccept (optionAccept test) draws = true) := by
  apply repetition_acceptance_probability S.boundedLaw (optionAccept test) hu
  simpa only [optionAccept_eq_true] using hp

end LowSpaceSubsetSum

end

end OAI
