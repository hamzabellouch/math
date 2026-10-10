import OAI.Analysis.FiniteFactor.CrossedProduct.ProjectionColumns
import OAI.Analysis.FiniteFactor.TailEstimate

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceColumn (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (b : Bool) (x : SourceCoordinate → ℝ) : SourceFiberHilbert :=
  if b then sourceComplementColumn p x else sourceProjectionColumn p x

theorem sourceColumn_coordinate_measurable
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (b : Bool) (k : ℤ) :
    Measurable (fun x => sourceColumn p b x k) := by
  cases b
  · exact sourceOperatorField_entry_measurable p k 0
  · exact measurable_const.sub (sourceOperatorField_entry_measurable p k 0)

theorem sourceColumn_square_hasSum
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (b : Bool) (x : SourceCoordinate → ℝ) (n : ℤ) :
    HasSum (fun k : ℤ => ‖sourceColumn p b x (n+k)‖^2) (‖sourceColumn p b x‖^2) := by
  have h : HasSum (fun k : ℤ => ‖sourceColumn p b x k‖^2) (‖sourceColumn p b x‖^2) := by
    simpa using lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (sourceColumn p b x)
  exact (Equiv.addLeft n).hasSum_iff.mpr h

/-- Actual endpoint square mass: integrable, and at most one. The shift is a
bijection of all integers; no finite coefficient cutoff is introduced. -/
theorem sourceColumn_square_mass (θ : SourceCoordinate → ℝ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) (j : ℕ) (b : Bool) (n : ℤ) :
    Integrable (fun ω => ∑' k : ℤ,
      ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (n+k)‖^2) (sourceBiasedLaw j) ∧
    (∫ ω, (∑' k : ℤ, ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (n+k)‖^2)
      ∂sourceBiasedLaw j) ≤ 1 := by
  let f := fun ω => ∑' k : ℤ, ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (n+k)‖^2
  have hm : Measurable f := Measurable.tsum (fun k =>
    (((sourceColumn_coordinate_measurable p b (n+k)).comp (sourceBiasedEndpoint_measurable _)).norm.pow_const 2))
  have h0 : ∀ ω, 0 ≤ f ω := fun ω => tsum_nonneg (fun _ => sq_nonneg _)
  have h1 : ∀ᵐ ω ∂sourceBiasedLaw j, f ω ≤ 1 := by
    filter_upwards [sourceBiasedEndpoint_ae j (fun _ => b) (sourceProjection_columns_norm θ hp hproj)] with ω hω
    have hn : ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω)‖ ≤ 1 := by
      cases b <;> simp only [sourceColumn,Bool.false_eq_true,↓reduceIte] <;> tauto
    rw [show f ω = ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω)‖^2 from
      (sourceColumn_square_hasSum p b _ n).tsum_eq]
    nlinarith [norm_nonneg (sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω))]
  have hi : Integrable f (sourceBiasedLaw j) := (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    (h1.mono fun ω h => by rwa [Real.norm_of_nonneg (h0 ω)])
  refine ⟨hi,?_⟩
  simpa using integral_mono_ae hi (integrable_const (1 : ℝ)) h1

end
end FiniteFactor

end OAI
