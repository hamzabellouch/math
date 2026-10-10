import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BranchClockGeometry
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarDormantZero

namespace OAI

/-! Every unused time cell has zero actual normalized planar velocity at
its waiting anchor. Spatial clearance and the final idle cell are explicit. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar
open ShearFlows PlanarHamiltonian PlanarRouting PlanarTiming Set

theorem translatedPoint_eq_shiftPoint : PlanarRouting.translatedPoint = shiftPoint := rfl

theorem normalized_sparseAnchor_zero (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    (i : ℕ) (hi : i < (actions (freshMachine I.1) (freshInput_valid hI).1).length + 1)
    (hne : ∀ k, (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k).val ≠ i)
    (s : ℝ) (hs : s ∈ Ico
      (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length i)
      (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length (i + 1))) :
    planarSlice (normalizedHamiltonian I hI) s
      (sparseAnchor (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b)
        (normalizedAnchors I hI b x) i) = 0 := by
  let n := (actions (freshMachine I.1) (freshInput_valid hI).1).length
  let J := branchIndices (freshMachine I.1) (freshInput_valid hI).1 b
  have hchart : sparseAnchor J (normalizedAnchors I hI b x) i ∈ clockRectangle.carrier :=
    normalizedAnchors_clock I hI b hx _
  have h₀ := hchart 0
  have h₁ := hchart 1
  have h₀' : sparseAnchor J (normalizedAnchors I hI b x) i 0 ∈ Ioo (0 : ℝ) 1 := by
    change ((1 / 8 : ℚ) : ℝ) ≤ _ ∧ _ ≤ ((7 / 8 : ℚ) : ℝ) at h₀
    constructor <;> norm_num at h₀ ⊢ <;> linarith [h₀.1, h₀.2]
  have h₁' : sparseAnchor J (normalizedAnchors I hI b x) i 1 ∈ Ioo (0 : ℝ) 1 := by
    change ((1 / 32 : ℚ) : ℝ) ≤ _ ∧ _ ≤ ((7 / 8 : ℚ) : ℝ) at h₁
    constructor <;> norm_num at h₁ ⊢ <;> linarith [h₁.1, h₁.2]
  by_cases hin : i < n
  · let ii : Fin n := ⟨i, hin⟩
    have hm := sparseAnchor_notMem_collar _ _ b hx ii hne
    have hm' : sparseAnchor J (normalizedAnchors I hI b x) i ∉
        (rectangleCollar (normalizedPulse I hI ii).rectangle (normalizedPulse I hI ii).collar).carrier := by
      intro he
      exact hm ((mem_translated_collar _ _ _ _).mp he)
    rw [normalizedSlice_on_cell I hI ii ⟨hs.1, hs.2.le⟩ _ h₀' h₁']
    exact Pulse.velocity_zero_of_notMem (normalizedPulse_valid I hI ii) hm' s
  · have he : i = n := by omega
    subst i
    apply normalizedSlice_on_tail I hI _ _ h₀' h₁'
    exact ⟨hs.1, (hs.2.trans_le (by rw [cut_last])).le⟩

end ForcedComputation.Recorder.Planar

end

end OAI
