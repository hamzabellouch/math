import OAI.Probability.InvariantIsing.Magnetic.MagneticGroupPath

namespace OAI

/-! Exact passage from attainable block proportions to the weighted
magnetic functional and overlap path. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators
namespace InvariantIsing

lemma sum_grouped_sites {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (f : A → ℝ) :
    (∑ j, f (group j)) = ∑ a, (spinGroupSize group a : ℝ) * f a := by
  rw [← Finset.sum_fiberwise Finset.univ group]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ _j ∈ Finset.univ.filter (fun j => group j = a), f a := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, spinGroupSize]

lemma average_grouped_sites {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (γ f : A → ℝ)
    (hcount : ∀ a, (spinGroupSize group a : ℝ) = N * γ a) :
    (N : ℝ)⁻¹ * (∑ j, f (group j)) = ∑ a, γ a * f a := by
  rw [sum_grouped_sites, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [hcount a]
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_mul]

lemma magneticGroupValue_eq_block {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (γ mag : A → ℝ)
    (hcount : ∀ a, (spinGroupSize group a : ℝ) = N * γ a) (h : FieldStep) :
    (N : ℝ)⁻¹ * (∑ j, constrainedFieldValue h (mag (group j))) =
      magneticGroupValue γ mag h :=
  average_grouped_sites hN group γ (fun a => constrainedFieldValue h (mag a)) hcount

lemma magneticGroupLevel_eq_block {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (γ mag : A → ℝ)
    (hcount : ∀ a, (spinGroupSize group a : ℝ) = N * γ a)
    (h : FieldStep) (i : Fin (h.depth+1)) :
    magneticBlockLevel h (fun j => mag (group j)) i = magneticGroupLevel γ mag h i :=
  average_grouped_sites hN group γ (fun a => magneticFieldLevel h (mag a) i) hcount

lemma magneticGroupPath_eq_block {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hcount : ∀ a, (spinGroupSize group a : ℝ) = N * γ a) (h : FieldStep) :
    magneticBlockPath hN h (fun j => mag (group j)) = magneticGroupPath γ mag hγ hγsum h := by
  apply (show Function.Injective OverlapPath.val from by
    intro a b hab
    cases a
    cases b
    cases hab
    rfl)
  funext t
  exact magneticGroupLevel_eq_block hN group γ mag hcount h (fieldLevelIndex h t)

end InvariantIsing

end

end OAI
