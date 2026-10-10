import OAI.Analysis.FiniteFactor.CrossedProduct.ColumnSquareMass
import OAI.Analysis.FiniteFactor.CrossedProduct.OmittedBadEvents

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The actual source columns and deterministic omitted-index masks satisfy
the infinite conditional square estimate in both orientations. -/
theorem sourceOmitted_masked_square (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n r : ℤ) (b : Bool) :
    (∫ ω, (∑' k : ℤ, (sourceOmittedBadEvent θ hθ j hphase n k b).indicator
      (fun ω => ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (r+k)‖^2) ω)
      ∂sourceBiasedLaw j) ≤ Real.exp (-(sourceStage j).L/400) := by
  let f := fun k ω => ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (r+k)‖^2
  have hfm (k : ℤ) : Measurable (f k) :=
    (((sourceColumn_coordinate_measurable p b (r+k)).comp (sourceBiasedEndpoint_measurable _)).norm.pow_const 2)
  have h0 (k : ℤ) (ω) : 0 ≤ f k ω := sq_nonneg _
  have hs (ω) : Summable (fun k => f k ω) := (sourceColumn_square_hasSum p b _ r).summable
  obtain ⟨hint,hbound⟩ := sourceColumn_square_mass θ hp hproj j b r
  have hf (k : ℤ) : Integrable (f k) (sourceBiasedLaw j) := by
    apply hint.mono' (hfm k).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (h0 k ω)]
      exact (hs ω).le_tsum k (fun i _ => h0 i ω)
  have hcond (k : ℤ) := (sourceOmittedBadEvent_condExp θ hθ j hphase).mono
    (fun ω h => h n k b)
  let m := (inferInstance : MeasurableSpace (SourceCoordinate → ℝ)).comap
    (sourceBiasedEndpoint (fun _ => b))
  have hstrong (k : ℤ) : StronglyMeasurable[m] (f k) := by
    have hh : Measurable[m] (f k) :=
      ((sourceColumn_coordinate_measurable p b (r+k)).norm.pow_const 2).comp
        (comap_measurable (sourceBiasedEndpoint (fun _ => b)))
    exact hh.stronglyMeasurable
  have hh := conditional_mask_tsum_integral_le
    (sourceBiasedEndpoint_measurable (fun _ => b)).comap_le hf hstrong
    h0 (fun k => sourceOmittedBadEvent_measurable θ hθ j hphase n k b)
    (Eventually.of_forall hs) hint hcond
  apply hh.trans
  exact (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le).trans_eq (mul_one _)

end
end FiniteFactor

end OAI
