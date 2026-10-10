import OAI.Analysis.FiniteFactor.CrossedProduct.PhaseMarginal
import OAI.Analysis.FiniteFactor.IndependentCount
import OAI.Analysis.FiniteFactor.CrossedProduct.StageCoupling

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal Classical
noncomputable section

def sourceBlockCoordinates (s : ℕ) : Finset SourceCoordinate :=
  Finset.univ.map ⟨fun i : Fin (sourceBlockSize s) => ⟨s,i⟩, by intro i j h; cases h; rfl⟩

@[simp] theorem sourceBlockCoordinates_card (s : ℕ) :
    (sourceBlockCoordinates s).card = sourceBlockSize s := by simp [sourceBlockCoordinates]

theorem mem_sourceBlockCoordinates {s : ℕ} {i : SourceCoordinate}
    (hi : i ∈ sourceBlockCoordinates s) : i.1 = s := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  rfl

def sourcePhaseMissSet (s : ℕ) (k : ℤ) : Set ℝ :=
  {t | 1-Int.fract ((k : ℝ)*t) ∉ Set.Icc (sourceWidth s 1) (1-sourceWidth s 1)}

theorem sourcePhaseMissSet_measurable (s : ℕ) (k : ℤ) : MeasurableSet (sourcePhaseMissSet s k) := by
  exact measurableSet_Icc.compl.preimage
    (measurable_const.sub (sourceFract_measurable.comp (by fun_prop)))

def sourceFewPhases (s : ℕ) (k : ℤ) : Set (SourceCoordinate → ℝ) :=
  {θ | (((sourceBlockCoordinates s).filter (fun i => θ i ∉ sourcePhaseMissSet s k)).card : ℝ) <
    (sourceBlockSize s : ℝ)/20}

def sourceMissCount (s : ℕ) : ℕ := Nat.ceil ((19/20 : ℝ)*(sourceBlockSize s : ℝ))

theorem sourceFewPhases_subset_misses (s : ℕ) (k : ℤ) :
    sourceFewPhases s k ⊆ coordinateMissEvent (sourceBlockCoordinates s) (sourceMissCount s)
      (fun _ => sourcePhaseMissSet s k) := by
  intro θ hθ
  apply mem_coordinateMissEvent_of_card
  apply Nat.ceil_le.mpr
  have hc := Finset.card_filter_add_card_filter_not (s := sourceBlockCoordinates s)
    (p := fun i => θ i ∈ sourcePhaseMissSet s k)
  have hcR : (((sourceBlockCoordinates s).filter (fun i => θ i ∈ sourcePhaseMissSet s k)).card : ℝ) +
      (((sourceBlockCoordinates s).filter (fun i => θ i ∉ sourcePhaseMissSet s k)).card : ℝ) =
      (sourceBlockSize s : ℝ) := by
        rw [sourceBlockCoordinates_card] at hc
        exact_mod_cast hc
  change (((sourceBlockCoordinates s).filter (fun i => θ i ∉ sourcePhaseMissSet s k)).card : ℝ) <
      (sourceBlockSize s : ℝ)/20 at hθ
  nlinarith

/-- The fixed-power failure probability in Proposition phases, for the actual
angle product measure. The ceiling records the exact finite counting step. -/
theorem sourceFewPhases_probability (s : ℕ) (k : ℤ)
    (hk : ((sourceBlockSize s : ℝ)*(sourceStageState s).K)/4 ≤ |(k : ℝ)|) :
    sourceAngleLaw (sourceFewPhases s k) ≤
      (2 : ℝ≥0∞)^sourceBlockSize s *
        (ENNReal.ofReal (10*sourceWidth s 1))^sourceMissCount s := by
  apply (measure_mono (sourceFewPhases_subset_misses s k)).trans
  simpa only [sourceBlockCoordinates_card] using
    coordinateMissEvent_bound (sourceBlockCoordinates s) (sourceMissCount s)
      (fun _ => sourcePhaseMissSet s k) (fun _ => sourcePhaseMissSet_measurable s k)
      (ENNReal.ofReal (10*sourceWidth s 1)) (by
        intro i hi
        have his := mem_sourceBlockCoordinates hi
        apply sourceAngle_phase_miss i k (sourceWidth s 1)
        · exact (by positivity : (0 : ℝ) ≤ 1/(sourceBlockSize s : ℝ)).trans (sourceWidth_bounds s 1).1
        · simpa only [his] using hk)

end
end FiniteFactor

end OAI
