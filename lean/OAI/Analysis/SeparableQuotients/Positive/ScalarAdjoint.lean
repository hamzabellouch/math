import OAI.Analysis.SeparableQuotients.Positive.RealAdjoint

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields
alias ball_subset_closure_image_of_adjoint_lower := Rows.ball_subset_closure_image_of_adjoint_lower
alias approx_preimage_of_adjoint_lower := Rows.approx_preimage_of_adjoint_lower
alias surjective_of_adjoint_lower := Rows.surjective_of_adjoint_lower
end SeparableQuotient.Positive.Fields

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields.Scalar
variable (𝕜 : Type*) [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]




theorem surjective_of_adjoint_lower [CompleteSpace X] (T : X →L[𝕜] Y) {c : ℝ}
    (hc : 0 < c) (hlower : ∀ h : StrongDual 𝕜 Y, c * ‖h‖ ≤ ‖h.comp T‖) :
    ∀ y : Y, ∃ x : X, T x = y ∧ ‖x‖ ≤ (2 / c) * ‖y‖ := by
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  let : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ 𝕜 Y
  have hlowerR (h : StrongDual ℝ Y) : c * ‖h‖ ≤ ‖h.comp (T.restrictScalars ℝ)‖ := by
    have hh := hlower (h.extendRCLike : StrongDual 𝕜 Y)
    have he : (h.extendRCLike : StrongDual 𝕜 Y).comp T =
        StrongDual.extendRCLike (h.comp (T.restrictScalars ℝ)) := by
      ext x
      simp only [ContinuousLinearMap.comp_apply, StrongDual.extendRCLike_apply,
        ContinuousLinearMap.coe_restrictScalars', map_smul]
    rw [he, StrongDual.norm_extendRCLike, StrongDual.norm_extendRCLike] at hh
    exact hh
  exact SeparableQuotient.Positive.Fields.surjective_of_adjoint_lower (T.restrictScalars ℝ) hc hlowerR
end SeparableQuotient.Positive.Fields.Scalar

end

end

end OAI
