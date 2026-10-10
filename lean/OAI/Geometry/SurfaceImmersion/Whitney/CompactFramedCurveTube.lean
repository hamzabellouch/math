import OAI.Geometry.SurfaceImmersion.Whitney.FramedCurveTube
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace OAI

/-! Uniform transverse width for the explicit target tube along a compact
regular segment of a smooth curve. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance compactTubeNormed : NormedAddCommGroup (Base × ℝ) := inferInstance
local instance compactTubeSpace : NormedSpace ℝ (Base × ℝ) := inferInstance

lemma framedCurveTube_regular_neighborhood {c : ℝ → (Fin 3 → ℝ)}
    (hc : ContDiff ℝ ∞ c) {a : Fin 3 → ℝ}
    (ha : ∀ t r : ℝ, r • deriv c t ≠ a) {K : Set ℝ}
    (hK : IsCompact K) (hreg : ∀ t ∈ K, deriv c t ≠ 0) :
    ∃ (r : ℝ) (U : Set ℝ), 0 < r ∧ IsOpen U ∧ K ⊆ U ∧
      ∀ x : Base, ‖x‖ < r → ∀ t ∈ U,
        Function.Bijective (fderiv ℝ (framedCurveTube c a) (x,t)) := by
  by_cases hne : K.Nonempty
  · obtain ⟨t₀,ht₀⟩ := hne
    have hR := framedCurveTube_regular_axis hc ha t₀ (hreg t₀ ht₀)
    let R : (Base × ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
      ContinuousLinearEquiv.ofBijective (fderiv ℝ (framedCurveTube c a) (0,t₀))
        (LinearMap.ker_eq_bot.mpr hR.1) (LinearMap.range_eq_top.mpr hR.2)
    let W : Set (Base × ℝ) :=
      {z | IsUnit (R.symm.toContinuousLinearMap.comp (fderiv ℝ (framedCurveTube c a) z))}
    have hcont : Continuous (fun z =>
        R.symm.toContinuousLinearMap.comp (fderiv ℝ (framedCurveTube c a) z)) :=
      continuous_const.clm_comp ((framedCurveTube_smooth hc a).continuous_fderiv (by simp))
    have hW : IsOpen W := Units.isOpen.preimage hcont
    have haxis : ({0} : Set Base) ×ˢ K ⊆ W := by
      rintro ⟨x,t⟩ ⟨hx,ht⟩
      obtain rfl : x = 0 := hx
      apply ContinuousLinearMap.isUnit_iff_bijective.mpr
      exact R.symm.bijective.comp (framedCurveTube_regular_axis hc ha t (hreg t ht))
    obtain ⟨V,U,hV,hU,h0V,hKU,hVU⟩ :=
      generalized_tube_lemma isCompact_singleton hK hW haxis
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hV 0 (h0V (by simp))
    refine ⟨r,U,hr,hU,hKU,?_⟩
    intro x hx t ht
    have hxV : x ∈ V := hball (by simpa [dist_zero_right] using hx)
    have hunit : IsUnit (R.symm.toContinuousLinearMap.comp
        (fderiv ℝ (framedCurveTube c a) (x,t))) := hVU ⟨hxV,ht⟩
    have hbij := ContinuousLinearMap.isUnit_iff_bijective.mp hunit
    have heq : (R : (Base × ℝ) → (Fin 3 → ℝ)) ∘
        (R.symm.toContinuousLinearMap.comp (fderiv ℝ (framedCurveTube c a) (x,t))) =
        fderiv ℝ (framedCurveTube c a) (x,t) := by
      funext v
      exact R.apply_symm_apply _
    rw [← heq]
    exact R.bijective.comp hbij
  · refine ⟨1,∅,by norm_num,isOpen_empty,?_,?_⟩
    · simpa only [not_nonempty_iff_eq_empty.mp hne] using (empty_subset (∅ : Set ℝ))
    · intro x hx t ht
      exact ht.elim

theorem exists_framed_curve_tube {c : ℝ → (Fin 3 → ℝ)}
    (hc : ContDiff ℝ ∞ c) {K : Set ℝ} (hK : IsCompact K)
    (hreg : ∀ t ∈ K, deriv c t ≠ 0) :
    ∃ (a : Fin 3 → ℝ) (r : ℝ) (U : Set ℝ),
      0 < r ∧ IsOpen U ∧ K ⊆ U ∧
      ContDiff ℝ ∞ (framedCurveTube c a) ∧
      (∀ t, framedCurveTube c a (0,t) = c t) ∧
      ∀ x : Base, ‖x‖ < r → ∀ t ∈ U,
        Function.Bijective (fderiv ℝ (framedCurveTube c a) (x,t)) := by
  obtain ⟨a,ha⟩ := exists_curve_transverse_vector (deriv c) (contDiff_infty_iff_deriv.mp hc).2
  obtain ⟨r,U,hr,hU,hKU,hI⟩ := framedCurveTube_regular_neighborhood hc ha hK hreg
  refine ⟨a,r,U,hr,hU,hKU,framedCurveTube_smooth hc a,?_,hI⟩
  intro t
  simp [framedCurveTube]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
