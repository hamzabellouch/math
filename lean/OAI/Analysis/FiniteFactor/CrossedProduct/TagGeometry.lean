import OAI.Analysis.FiniteFactor.CrossedProduct.PhaseFirst
import OAI.Analysis.FiniteFactor.BiasedPairs.RealIdentity
import OAI.Analysis.FiniteFactor.CrossedProduct.Attenuation
import OAI.Analysis.FiniteFactor.Coupling.BadEvents

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem SourceAngles.tag_threshold {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ)
    (j : ℕ) (k : ℤ) (hk : ((sourceStageState j).K : ℝ) ≤ |(k : ℝ)|)
    (hhi : |(k : ℝ)| ≤ ((sourceBlockSize j : ℝ)*(sourceStageState j).K)/4)
    (i : Fin (sourceBlockSize j)) :
    1-Int.fract ((k : ℝ)*θ ⟨j,i⟩) ∈ Set.Icc (1/(sourceBlockSize j : ℝ)) (1-1/(sourceBlockSize j : ℝ)) := by
  have hm := sourceBlockSize_pos j
  have hK := sourceCutoff_pos j
  apply phase_threshold_of_abs (one_div_pos.mpr hm)
  · apply (div_le_iff₀ hm).mpr
    have hh : (100 : ℝ) ≤ sourceBlockSize j := by exact_mod_cast (sourceStage j).m_ge_100
    linarith
  · rw [abs_mul,abs_of_nonneg (hθ.nonneg ⟨j,i⟩)]
    calc
      1/(sourceBlockSize j : ℝ) = (sourceStageState j).K *
          (1/((sourceBlockSize j : ℝ)*(sourceStageState j).K)) := by field_simp
      _ ≤ |(k : ℝ)| * θ ⟨j,i⟩ :=
        mul_le_mul hk (hθ ⟨j,i⟩).1 (by positivity) (abs_nonneg _)
  · rw [abs_mul,abs_of_nonneg (hθ.nonneg ⟨j,i⟩)]
    calc
      |(k : ℝ)| * θ ⟨j,i⟩ ≤ (((sourceBlockSize j : ℝ)*(sourceStageState j).K)/4) *
          (2/((sourceBlockSize j : ℝ)*(sourceStageState j).K)) :=
        mul_le_mul hhi (hθ ⟨j,i⟩).2 (hθ.nonneg _) (by positivity)
      _ = 1/2 := by field_simp; norm_num

/-- Endpoint consequence of a source tag; the label implication and positive
probability are separate obligations, not encoded into this predicate. -/
def sourceTagEndpointEvent (j : ℕ) : Set SourceBiasedSample :=
  {ω | ∃ i : Fin (sourceBlockSize j),
    sourceBiasedEndpoint (fun _ => false) ω ⟨j,i⟩ < 1/(sourceBlockSize j : ℝ) ∧
    1-1/(sourceBlockSize j : ℝ) ≤ sourceBiasedEndpoint (fun _ => true) ω ⟨j,i⟩}

theorem sourceTagEndpointEvent_measurable (j : ℕ) : MeasurableSet (sourceTagEndpointEvent j) := by
  have he : sourceTagEndpointEvent j = ⋃ i : Fin (sourceBlockSize j),
      {ω | sourceBiasedEndpoint (fun _ => false) ω ⟨j,i⟩ < 1/(sourceBlockSize j : ℝ) ∧
        1-1/(sourceBlockSize j : ℝ) ≤ sourceBiasedEndpoint (fun _ => true) ω ⟨j,i⟩} := by
    ext ω
    simp [sourceTagEndpointEvent]
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  exact (measurableSet_lt ((measurable_pi_apply ⟨j,i⟩).comp (sourceBiasedEndpoint_measurable _))
    measurable_const).inter
    (measurableSet_le measurable_const ((measurable_pi_apply ⟨j,i⟩).comp (sourceBiasedEndpoint_measurable _)))

/-- Actual cocycle attenuation on the endpoint event, simultaneously at all
near-range signed integer indices. No cutoff is applied to the ratio. -/
theorem sourceTagEndpoint_attenuation (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ω ∈ sourceTagEndpointEvent j → ∀ k : ℤ,
      ((sourceStageState j).K : ℝ) ≤ |(k : ℝ)| →
      |(k : ℝ)| ≤ ((sourceBlockSize j : ℝ)*(sourceStageState j).K)/4 →
      sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => true) ω) /
        sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => false) ω) ≤
          Real.exp (-(sourceStage j).L) := by
  have hcube := CouplingParameters.vectorEndpoint_unitCube
    (fun i : SourceCoordinate => stagedCouplingParameters j i.1)
  filter_upwards [
    ae_of_ae_map (sourceBiasedEndpoint_measurable (fun _ => false)).aemeasurable (hcube (fun _ => false)),
    ae_of_ae_map (sourceBiasedEndpoint_measurable (fun _ => true)).aemeasurable (hcube (fun _ => true)),
    sourceBiasedLaw_ordered j,
    sourceBiasedEndpoint_ae j (fun _ => false) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => true) (ae_finiteFloorSupport θ hθ.summable)]
    with ω hxc hyc hxy hfx hfy
  rintro ⟨i,hxi,hyi⟩ k hk hhi
  have ht := hθ.tag_threshold j k hk hhi i
  have hatt := sourceCocycle_crossing_attenuation θ sourceLogWeight sourceLogWeight_nonneg
    hfx hfy hxy k ⟨j,i⟩ (hxc _) (hyc _) ⟨hxi.trans_le ht.1,ht.2.trans hyi⟩
  exact hatt.trans (Real.exp_le_exp.mpr (neg_le_neg (le_max_left _ _)))

end
end FiniteFactor

end OAI
