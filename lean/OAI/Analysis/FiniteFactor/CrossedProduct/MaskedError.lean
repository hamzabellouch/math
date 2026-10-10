import OAI.Analysis.FiniteFactor.CrossedProduct.MaskedSquareMass
import OAI.Analysis.FiniteFactor.CountableMaskedError

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Both source expected-error estimates for the full infinite coefficient
sum. b=false,r=0,s=n gives the first orientation; b=true,r=n,s=0 gives the
second, after commuting the scalar product. -/
theorem sourceOmitted_masked_error (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n r s : ℤ) (b : Bool) :
    let error := fun ω => ∑' k : ℤ, (sourceOmittedBadEvent θ hθ j hphase n k b).indicator
      (fun ω => ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (r+k)‖ *
        ‖sourceColumn p (!b) (sourceBiasedEndpoint (fun _ => !b) ω) (s+k)‖) ω
    Integrable error (sourceBiasedLaw j) ∧
      (∫ ω, error ω ∂sourceBiasedLaw j) ≤ Real.exp (-(sourceStage j).L/800) := by
  let H := fun k => sourceOmittedBadEvent θ hθ j hphase n k b
  let u := fun k ω => ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (r+k)‖
  let g := fun k ω => ‖sourceColumn p (!b) (sourceBiasedEndpoint (fun _ => !b) ω) (s+k)‖
  let f := fun k => (H k).indicator (u k)
  have hu (k) : Measurable (u k) :=
    ((sourceColumn_coordinate_measurable p b (r+k)).comp (sourceBiasedEndpoint_measurable _)).norm
  have hg (k) : Measurable (g k) :=
    ((sourceColumn_coordinate_measurable p (!b) (s+k)).comp (sourceBiasedEndpoint_measurable _)).norm
  have hH (k) : MeasurableSet (H k) := sourceOmittedBadEvent_measurable θ hθ j hphase n k b
  have hf (k) : Measurable (f k) := (hu k).indicator (hH k)
  have hf0 (k ω) : 0 ≤ f k ω := by
    by_cases h : ω ∈ H k <;> simp [f,h,u]
  have hule (k ω) : (f k ω)^2 ≤ (u k ω)^2 := by
    by_cases h : ω ∈ H k <;> simp [f,h,sq_nonneg]
  have hhe (k ω) : (f k ω)^2 = (H k).indicator (fun ω => (u k ω)^2) ω := by
    by_cases h : ω ∈ H k <;> simp [f,h]
  have hus (ω) : Summable (fun k => (u k ω)^2) := (sourceColumn_square_hasSum p b _ r).summable
  have hfs (ω) : Summable (fun k => (f k ω)^2) :=
    (hus ω).of_nonneg_of_le (fun k => sq_nonneg _) (fun k => hule k ω)
  have hsumle (ω) : (∑' k, (f k ω)^2) ≤ ∑' k, (u k ω)^2 :=
    (hfs ω).tsum_le_tsum (fun k => hule k ω) (hus ω)
  have hfi : Integrable (fun ω => ∑' k, (f k ω)^2) (sourceBiasedLaw j) := by
    apply (sourceColumn_square_mass θ hp hproj j b r).1.mono'
      (Measurable.tsum (fun k => (hf k).pow_const 2)).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (tsum_nonneg (fun k => sq_nonneg _))]
      exact hsumle ω
  have hfm : (∫ ω, (∑' k, (f k ω)^2) ∂sourceBiasedLaw j) ≤ Real.exp (-(sourceStage j).L/400) := by
    simp_rw [hhe]
    exact sourceOmitted_masked_square θ hθ hp hproj j hphase n r b
  have hg1 : ∀ᵐ ω ∂sourceBiasedLaw j, (∑' k, (g k ω)^2) ≤ 1 := by
    filter_upwards [sourceBiasedEndpoint_ae j (fun _ => !b) (sourceProjection_columns_norm θ hp hproj)] with ω hω
    have hn : ‖sourceColumn p (!b) (sourceBiasedEndpoint (fun _ => !b) ω)‖ ≤ 1 := by
      cases b <;> simp only [Bool.not_false,Bool.not_true,sourceColumn,Bool.false_eq_true,↓reduceIte] <;> tauto
    rw [(sourceColumn_square_hasSum p (!b) _ s).tsum_eq]
    nlinarith [norm_nonneg (sourceColumn p (!b) (sourceBiasedEndpoint (fun _ => !b) ω))]
  obtain ⟨hi,hb⟩ := countable_error_integral_le f g (Real.exp (-(sourceStage j).L/400))
    hf hg hf0 (fun k ω => norm_nonneg _) (Eventually.of_forall hfs)
    (Eventually.of_forall fun ω => (sourceColumn_square_hasSum p (!b) _ s).summable) hfi hfm hg1
  have he (k ω) : f k ω*g k ω = (H k).indicator (fun ω => u k ω*g k ω) ω := by
    by_cases h : ω ∈ H k <;> simp [f,h]
  simp_rw [he] at hi hb
  refine ⟨hi,hb.trans_eq ?_⟩
  rw [Real.sqrt_eq_rpow,← Real.exp_mul]
  congr 1
  ring

end
end FiniteFactor

end OAI
