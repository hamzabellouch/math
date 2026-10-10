import OAI.Analysis.OperatorAlgebra.UnitaryOrbitMean

namespace OAI

/-! Linearity, positivity and the fixed points of unitary orbit averaging. -/

noncomputable section
open Filter
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma unitaryOrbitMean_add (ω : Ultrafilter ℕ) (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (T R : H →L[ℂ] H) :
    unitaryOrbitMean ω U hU (T + R) =
      unitaryOrbitMean ω U hU T + unitaryOrbitMean ω U hU R := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [add_apply, inner_add_left, unitaryOrbitMean_inner]
  have h : unitaryOrbitCoefficient U hU (T + R) x y =
      unitaryOrbitCoefficient U hU T x y + unitaryOrbitCoefficient U hU R x y := by
    ext t
    simp only [unitaryOrbitCoefficient_apply, add_apply, inner_add_left,
      BoundedContinuousFunction.add_apply]
  rw [h, complexSymmetricMean_add]

lemma unitaryOrbitMean_smul (ω : Ultrafilter ℕ) (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (c : ℂ) (T : H →L[ℂ] H) :
    unitaryOrbitMean ω U hU (c • T) = c • unitaryOrbitMean ω U hU T := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [smul_apply, inner_smul_left, unitaryOrbitMean_inner]
  have h : unitaryOrbitCoefficient U hU (c • T) x y =
      star c • unitaryOrbitCoefficient U hU T x y := by
    ext t
    simp only [unitaryOrbitCoefficient_apply, smul_apply, inner_smul_left,
      BoundedContinuousFunction.smul_apply, smul_eq_mul, starRingEnd_apply]
  rw [h, complexSymmetricMean_smul]
  rfl

def unitaryOrbitMeanCLM (ω : Ultrafilter ℕ) (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  ({ toFun := unitaryOrbitMean ω U hU
     map_add' := unitaryOrbitMean_add ω U hU
     map_smul' := unitaryOrbitMean_smul ω U hU } :
     (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)).mkContinuous 2
    (unitaryOrbitMean_norm_le ω U hU)

lemma unitaryOrbitMean_fix (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (U : ℝ → H ≃ₗᵢ[ℂ] H) (hU : ∀ x, Continuous (fun t => U t x))
    (T : H →L[ℂ] H) (hT : ∀ t x, T (U t x) = U t (T x)) :
    unitaryOrbitMean ω U hU T = T := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [unitaryOrbitMean_inner]
  have h : unitaryOrbitCoefficient U hU T x y =
      BoundedContinuousFunction.const ℝ (inner ℂ (T x) y) := by
    ext t
    simp only [unitaryOrbitCoefficient_apply, hT, LinearIsometryEquiv.inner_map_map,
      BoundedContinuousFunction.const_apply]
  rw [h, complexSymmetricMean_const ω hω]

lemma unitaryOrbitMean_positive (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (U : ℝ → H ≃ₗᵢ[ℂ] H) (hU : ∀ x, Continuous (fun t => U t x))
    (T : H →L[ℂ] H) (hT : 0 ≤ T) : 0 ≤ unitaryOrbitMean ω U hU T := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hn : 0 ≤ inner ℂ (unitaryOrbitMean ω U hU T x) x := by
    rw [unitaryOrbitMean_inner]
    apply complexSymmetricMean_nonneg ω hω
    intro t
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).inner_nonneg_left _
  exact ⟨Complex.ext rfl hn.2, hn.1⟩

lemma unitaryOrbitMean_commutes (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (U : ℝ → H ≃ₗᵢ[ℂ] H) (hU : ∀ x, Continuous (fun t => U t x))
    (hadd : ∀ t s x, U (t + s) x = U t (U s x))
    (T : H →L[ℂ] H) (s : ℝ) (x : H) :
    U s (unitaryOrbitMean ω U hU T x) = unitaryOrbitMean ω U hU T (U s x) := by
  apply ext_inner_right ℂ
  intro z
  obtain ⟨y, rfl⟩ := (U s).surjective z
  rw [(U s).inner_map_map, unitaryOrbitMean_inner, unitaryOrbitMean_inner]
  have h : unitaryOrbitCoefficient U hU T (U s x) (U s y) =
      complexTranslateBCF (unitaryOrbitCoefficient U hU T x y) s := by
    ext t
    change inner ℂ (T (U t (U s x))) (U t (U s y)) =
      inner ℂ (T (U (t + s) x)) (U (t + s) y)
    rw [hadd, hadd]
  rw [h, complexSymmetricMean_translate ω hω]

end WeakPureInfiniteness

end

end OAI
