import OAI.Analysis.CircleDomains.Rigidity.EnclosedCircleChords
import OAI.Analysis.CircleDomains.Rigidity.AxialBandFlux

namespace OAI

/-! The sum over crossed inner circles is the finite sum of their
zero-extended axial increments. -/
open Set Function Metric
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem enclosed_crossing_sum {κ : Type*} [Fintype κ]
    (i : Fin 2) (F : ℂ → ℂ) (c : κ → ℂ) (r : κ → ℝ) {R y : ℝ} (hR : 0 ≤ R)
    (hy : y ∈ Icc (-R) R)
    (hin : ∀ j, closedBall (c j) (r j) ⊆ closedBall 0 R) :
    (∑ j ∈ crossingDisks (fun j => axialSwap i (c j)) r y
      (axialChord i 0 R y).1 (axialChord i 0 R y).2, axialCircleIncrement i F (c j) (r j) y) =
      ∑ j, axialBandIncrement i F (c j) (r j) y := by
  classical
  simp only [crossingDisks,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  have he : (∃ x ∈ Icc (axialChord i 0 R y).1 (axialChord i 0 R y).2,
      (⟨x,y⟩ : ℂ) ∈ closedBall (axialSwap i (c j)) (r j)) ↔
      y ∈ Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j) := by
    simpa only [mem_crossingDisks] using enclosed_crossing_iff i c r hR hy hin j
  rw [he]
  rfl

end CircleDomainRigidity

end

end OAI
