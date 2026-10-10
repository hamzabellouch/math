import OAI.Analysis.CircleDomains.Selection.MeanGeometricIndex

namespace OAI

/-! The compact arc family's geometric index bound also bounds every
mean branch on a bounded logarithmic chart. -/

open Set Function MeasureTheory

noncomputable section
namespace CircleDomainRigidity

theorem bounded_meanGeometricIndex_on_chart
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K)
    {X : Type*} (S : Set X) (L : X → ClosedUpperHalfPlane) (R : ℝ)
    (hR : ∀ x ∈ S, ‖(L x).val‖ ≤ R) :
    ∃ M : ℝ, ∀ x ∈ S, |meanGeometricIndex hsch K hKS η (L x)| ≤ M := by
  let T := max R 0
  have hT : 0 ≤ T := le_max_right _ _
  obtain ⟨M, hM⟩ := compact_geometricRayIndex_bound hsch K hK hKS T T hT hT
  refine ⟨M, ?_⟩
  intro x hx
  have hb : ‖(L x).val‖ ≤ T := (hR x hx).trans (le_max_left _ _)
  have hi : ∀ᵐ γ : K ∂(η : Measure K),
      ‖(geometricRayIndex hsch γ.val (hKS γ.property) (L x).val : ℝ)‖ ≤ M := by
    apply Filter.Eventually.of_forall
    intro γ
    simpa only [Complex.re_add_im, Real.norm_eq_abs] using
      hM γ (L x).val.re (L x).val.im ((Complex.abs_re_le_norm _).trans hb)
        (L x).property ((Complex.im_le_norm _).trans hb)
  simpa only [meanGeometricIndex, Real.norm_eq_abs, measureReal_def, measure_univ,
    ENNReal.toReal_one, mul_one] using norm_integral_le_of_norm_le_const hi

end CircleDomainRigidity

end

end OAI
