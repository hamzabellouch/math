import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarRecorder

namespace OAI

/-! The geometric branch implementing a machine step retains its source and
target control states. These identities supply the all-time observer guard. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar
open ShearFlows Radix

theorem step_branch {M : Alternating.Machine} {hM : M.WellFormed}
    {C D : Configuration (State M) (Alphabet M)} (h : Step (finiteMachine M hM) C D) :
    ∃ b : Branch (finiteMachine M hM), b.source = C.control ∧ b.target = D.control ∧
      point M hM C ∈ (instruction M hM b).source.carrier ∧
      (instruction M hM b).affine (point M hM C) = point M hM D := by
  obtain ⟨q, a, d, hl, rfl⟩ := h
  let b : Branch (finiteMachine M hM) :=
    ⟨C.control, C.tape C.head, q, a, d, C.tape (C.head - 1), hl⟩
  have hdigits : ∀ a, 0 ≤ radixDigit M a ∧ radixDigit M a ≤ radixBase M - 1 := by
    intro a
    exact ⟨(radixDigit_bounds_rat M a).1, by linarith [(radixDigit_bounds_rat M a).2]⟩
  have hx : codedPoint M C ∈ (geometricInstruction M hM b).source.carrier :=
    branchInstruction_contains (radixBase_gt_one M) hdigits (bandScale_pos M).le
      (stateOffset M) b C rfl rfl rfl
  have ha : (geometricInstruction M hM b).affine (codedPoint M C) =
      codedPoint M ⟨q, C.head + d, Function.update C.tape C.head a⟩ :=
    branchInstruction_step (radixBase_gt_one M) hdigits (bandScale M) (stateOffset M) b C rfl rfl rfl
  refine ⟨b, rfl, rfl, ?_, ?_⟩
  · exact PlanarConjugacy.mem_box_of_mem (compression_pos M hM).le (by norm_num) hx
  · change (PlanarConjugacy.instruction _ _ _ _ _).affine
      (PlanarConjugacy.map _ _ _ _ (codedPoint M C)) = _
    rw [PlanarConjugacy.instruction_conjugacy _ _ _ _ _
      (geometricInstruction_factor_pos M hM b).ne', ha]
    rfl

end ForcedComputation.Recorder.Planar

end

end OAI
