import OAI.Geometry.SurfaceImmersion.Whitney.VaryingFramedCurveTube
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace OAI

/-! One transverse radius works for all points of a compact regular
 segment of the ruled target tube. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem compact_varying_frame_tube {c a : ℝ → (Fin 3 → ℝ)}
    (hc : ContDiff ℝ ∞ c) (ha : ContDiff ℝ ∞ a) {K : Set ℝ}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hv : ∀ t ∈ K, deriv c t ≠ 0) (htrans : ∀ t ∈ K, ∀ r : ℝ, r • deriv c t ≠ a t) :
    ∃ (r : ℝ) (U : Set ℝ), 0 < r ∧ IsOpen U ∧ K ⊆ U ∧
      ∀ x : Base, ‖x‖ < r → ∀ t ∈ U,
        Function.Bijective (fderiv ℝ (varyingFramedCurveTube c a) (x,t)) := by
  obtain ⟨t₀,ht₀⟩ := hne
  have hR := varyingFramedCurveTube_regular_axis hc ha (hv t₀ ht₀) (htrans t₀ ht₀)
  let R : (Base × ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ (varyingFramedCurveTube c a) (0,t₀))
      (LinearMap.ker_eq_bot.mpr hR.1) (LinearMap.range_eq_top.mpr hR.2)
  let W : Set (Base × ℝ) :=
    {z | IsUnit (R.symm.toContinuousLinearMap.comp (fderiv ℝ (varyingFramedCurveTube c a) z))}
  have hcont : Continuous (fun z =>
      R.symm.toContinuousLinearMap.comp (fderiv ℝ (varyingFramedCurveTube c a) z)) :=
    continuous_const.clm_comp ((varyingFramedCurveTube_smooth hc ha).continuous_fderiv (by simp))
  have hW : IsOpen W := Units.isOpen.preimage hcont
  have haxis : ({0} : Set Base) ×ˢ K ⊆ W := by
    rintro ⟨x,t⟩ ⟨hx,ht⟩
    obtain rfl : x = 0 := hx
    apply ContinuousLinearMap.isUnit_iff_bijective.mpr
    exact R.symm.bijective.comp (varyingFramedCurveTube_regular_axis hc ha (hv t ht) (htrans t ht))
  obtain ⟨V,U,hV,hU,h0V,hKU,hVU⟩ :=
    generalized_tube_lemma isCompact_singleton hK hW haxis
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hV 0 (h0V (by simp))
  refine ⟨r,U,hr,hU,hKU,?_⟩
  intro x hx t ht
  have hxV : x ∈ V := hball (by simpa [dist_zero_right] using hx)
  have hunit : IsUnit (R.symm.toContinuousLinearMap.comp
      (fderiv ℝ (varyingFramedCurveTube c a) (x,t))) := hVU ⟨hxV,ht⟩
  have hbij := ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  have heq : (R : (Base × ℝ) → (Fin 3 → ℝ)) ∘
      (R.symm.toContinuousLinearMap.comp (fderiv ℝ (varyingFramedCurveTube c a) (x,t))) =
      fderiv ℝ (varyingFramedCurveTube c a) (x,t) := by
    funext v
    exact R.apply_symm_apply _
  rw [← heq]
  exact R.bijective.comp hbij

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
