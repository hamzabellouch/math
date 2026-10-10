import OAI.Analysis.FiniteFactor.CrossedProduct.FiniteCocycleBounds
import OAI.Analysis.FiniteFactor.BiasedPairs.RealIdentity

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- The source margin 2K_j/N_s. At s=j it is exactly 2/m_j. -/
def sourceExclusionWidth (j : ℕ) (i : SourceCoordinate) : ℝ :=
  2*(sourceStageState j).K/((sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K)

def sourceBoundaryEvent (j : ℕ) : Set SourceBiasedSample :=
  {ω | ∀ i : SourceCoordinate, j ≤ i.1 →
    sourceBiasedEndpoint (fun _ => false) ω i < 1-sourceExclusionWidth j i ∧
    sourceExclusionWidth j i < sourceBiasedEndpoint (fun _ => true) ω i}

theorem sourceExclusionWidth_current (j : ℕ) (i : Fin (sourceBlockSize j)) :
    sourceExclusionWidth j ⟨j,i⟩ = 2/(sourceBlockSize j : ℝ) := by
  unfold sourceExclusionWidth
  field_simp [(sourceCutoff_pos j).ne']

theorem sourceBoundaryEvent_measurable (j : ℕ) : MeasurableSet (sourceBoundaryEvent j) := by
  simp only [sourceBoundaryEvent,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _hi
  exact (measurableSet_lt ((measurable_pi_apply i).comp (sourceBiasedEndpoint_measurable _))
    measurable_const).inter
    (measurableSet_lt measurable_const ((measurable_pi_apply i).comp (sourceBiasedEndpoint_measurable _)))

/-- The actual source margins force zero later-coordinate floors for both
signs needed by the finite coefficient bound. -/
theorem sourceBoundary_floor_zero (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (ω : SourceBiasedSample) (he : ω ∈ sourceBoundaryEvent j)
    (hxc : ∀ i, sourceBiasedEndpoint (fun _ => false) ω i ∈ Set.Ico 0 1)
    (hyc : ∀ i, sourceBiasedEndpoint (fun _ => true) ω i ∈ Set.Ico 0 1)
    (v : ℤ) (hv : 0 ≤ v) (hvK : (v : ℝ) ≤ (sourceStageState j).K) :
    ∀ i : SourceCoordinate, j ≤ i.1 →
      coordinateFloor θ v (sourceBiasedEndpoint (fun _ => false) ω) i = 0 ∧
      coordinateFloor θ (-v) (sourceBiasedEndpoint (fun _ => true) ω) i = 0 := by
  intro i hi
  have hv0 : (0 : ℝ) ≤ v := by exact_mod_cast hv
  have hn := mul_nonneg hv0 (hθ.nonneg i)
  have hu : (v : ℝ)*θ i ≤ sourceExclusionWidth j i := by
    calc
      (v : ℝ)*θ i ≤ ((sourceStageState j).K : ℝ) *
          (2/((sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K)) :=
        mul_le_mul hvK (hθ i).2 (hθ.nonneg i) (Nat.cast_nonneg _)
      _ = _ := by unfold sourceExclusionWidth; ring
  obtain ⟨hx,hy⟩ := he i hi
  constructor
  · apply Int.floor_eq_zero_iff.mpr
    change 0 ≤ sourceBiasedEndpoint (fun _ => false) ω i + (v : ℝ)*θ i ∧
      sourceBiasedEndpoint (fun _ => false) ω i + (v : ℝ)*θ i < 1
    constructor <;> linarith [(hxc i).1]
  · apply Int.floor_eq_zero_iff.mpr
    change 0 ≤ sourceBiasedEndpoint (fun _ => true) ω i + ((-v : ℤ) : ℝ)*θ i ∧
      sourceBiasedEndpoint (fun _ => true) ω i + ((-v : ℤ) : ℝ)*θ i < 1
    rw [Int.cast_neg]
    constructor <;> linarith [(hyc i).2]

end
end FiniteFactor

end OAI
