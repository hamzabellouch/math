import Mathlib

namespace OAI

/-! Positive-functional nullspace facts used in the proof of KR02 Lemma 7.17(ii).
These work in the nonunital algebra and use its approximate unit. -/

noncomputable section
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Complexification of a real functional on the self-adjoint part. -/
def realFunctionalComplexification (f : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (f (realPart a) : ℂ) + Complex.I * (f (imaginaryPart a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add]; ring
  map_smul' c a := by
    simp only [realPart_smul, imaginaryPart_smul,
      map_sub, map_add, map_smul, smul_eq_mul, Complex.ofReal_sub,
      Complex.ofReal_add, Complex.ofReal_mul]
    apply Complex.ext <;> simp

lemma realFunctionalComplexification_apply
    (f : selfAdjoint A →ₗ[ℝ] ℝ) (a : selfAdjoint A) :
    realFunctionalComplexification f (a : A) = (f a : ℂ) := by
  have hr : realPart (a : A) = a := Subtype.ext a.property.coe_realPart
  simp [realFunctionalComplexification, hr, a.property.imaginaryPart]

variable [PartialOrder A] [StarOrderedRing A]

/-- Positivity alone suffices for the complexification; no unit or normalized
state hypothesis is required. -/
def positiveRealComplexification (f : selfAdjoint A →ₗ[ℝ] ℝ)
    (hf : ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ f a) : A →ₚ[ℂ] ℂ where
  toLinearMap := realFunctionalComplexification f
  monotone' := by
    intro a b hab
    change realFunctionalComplexification f a ≤ realFunctionalComplexification f b
    rw [← sub_nonneg, ← map_sub]
    let x : selfAdjoint A := ⟨b - a, IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hab)⟩
    change 0 ≤ realFunctionalComplexification f (x : A)
    rw [realFunctionalComplexification_apply]
    exact Complex.zero_le_real.mpr (hf x (sub_nonneg.mpr hab))

lemma positiveRealComplexification_apply
    (f : selfAdjoint A →ₗ[ℝ] ℝ)
    (hf : ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ f a)
    (a : selfAdjoint A) : positiveRealComplexification f hf (a : A) = (f a : ℂ) :=
  realFunctionalComplexification_apply f a

lemma positiveFunctional_eq_zero_of_square (φ : A →ₚ[ℂ] ℂ) (a : A)
    (ha : φ (star a * a) = 0) : φ a = 0 := by
  have hzero (e : A) : φ (star e * a) = 0 := by
    have h := PositiveLinearMap.norm_map_star_mul_le φ e a
    rw [ha, norm_zero, Real.sqrt_zero, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  let l := CStarAlgebra.approximateUnit A
  have hl := CStarAlgebra.increasingApproximateUnit A
  let : l.NeBot := hl.toIsApproximateUnit.neBot
  have hlim : Tendsto (fun e => φ (e * a)) l (𝓝 (φ a)) :=
    (map_continuous φ).continuousAt.tendsto.comp (hl.tendsto_mul_right a)
  have hevent : ∀ᶠ e in l, φ (e * a) = 0 := by
    filter_upwards [hl.eventually_star_eq] with e he
    simpa only [he] using hzero e
  exact tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hevent))

lemma positiveRealFunctional_eq_zero_of_square
    (f : selfAdjoint A →ₗ[ℝ] ℝ)
    (hf : ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ f a)
    (a : selfAdjoint A)
    (ha : f ⟨star (a : A) * (a : A), (star_mul_self_nonneg (a : A)).isSelfAdjoint⟩ = 0) :
    f a = 0 := by
  let φ := positiveRealComplexification f hf
  have hsquare : φ (star (a : A) * (a : A)) = 0 := by
    change positiveRealComplexification f hf
      ((⟨star (a : A) * (a : A), (star_mul_self_nonneg (a : A)).isSelfAdjoint⟩ : selfAdjoint A) : A) = 0
    rw [positiveRealComplexification_apply, ha, Complex.ofReal_zero]
  have h := positiveFunctional_eq_zero_of_square φ (a : A) hsquare
  change positiveRealComplexification f hf (a : A) = 0 at h
  rw [positiveRealComplexification_apply] at h
  exact Complex.ofReal_eq_zero.mp h

end WeakPureInfiniteness

end

end OAI
