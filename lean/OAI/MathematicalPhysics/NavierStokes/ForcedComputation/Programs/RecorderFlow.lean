import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FiniteGeometry
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicFlow
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Main

namespace OAI

/-! The finite recorder's actual tape configurations are the integer-time
positions of the smooth periodic shear flow. -/

noncomputable section

namespace ForcedComputation.Recorder

open ShearFlows Radix

def codedPoint (M : Alternating.Machine)
    (C : Configuration (State M) (Alphabet M)) : Plane :=
  configurationPoint (bandScale M) (radixBase M) (radixDigit M) (stateOffset M) C

theorem Step.flow_one {M : Alternating.Machine} {hM : M.WellFormed}
    {C D : Configuration (State M) (Alphabet M)}
    (h : Step (finiteMachine M hM) C D)
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow (compiledInput M hM).period
      (compiledInput M hM).realizingVelocity Φ) :
    Φ 1 (atHeight (codedPoint M C) (1 / 2)) = atHeight (codedPoint M D) (1 / 2) := by
  obtain ⟨q, a, d, hl, rfl⟩ := h
  let b : Branch (finiteMachine M hM) :=
    ⟨C.control, C.tape C.head, q, a, d, C.tape (C.head - 1), hl⟩
  have hd := compiledInput_valid M hM
  have hmem := geometricInstruction_mem M hM b
  have hB := radixBase_gt_one M
  have hdigits : ∀ a, 0 ≤ radixDigit M a ∧ radixDigit M a ≤ radixBase M - 1 := by
    intro a
    exact ⟨(radixDigit_bounds_rat M a).1, by linarith [(radixDigit_bounds_rat M a).2]⟩
  have hc : codedPoint M C ∈ (geometricInstruction M hM b).source.carrier :=
    branchInstruction_contains hB hdigits (bandScale_pos M).le (stateOffset M) b C rfl rfl rfl
  have htube := sourceTube_contains (geometricInstruction M hM b)
    (compiledInput M hM).codingHeight (δ := ((compiledInput M hM).tubeRadius : ℝ))
    (by exact_mod_cast tubeRadius_pos hd)
    (Set.mem_image_of_mem (fun X => atHeight X (compiledInput M hM).codingHeight) hc)
  have he := realizingVelocity_periodMap hd hΦ hmem htube
  have ha := branchInstruction_step hB hdigits (bandScale M) (stateOffset M) b C rfl rfl rfl
  simp only [atHeight_horizontal] at he
  change Φ 1 (atHeight (codedPoint M C) (compiledInput M hM).codingHeight) =
    atHeight ((geometricInstruction M hM b).affine (codedPoint M C))
      (compiledInput M hM).codingHeight at he
  have ha' : (geometricInstruction M hM b).affine (codedPoint M C) =
      codedPoint M ⟨q, C.head + d, Function.update C.tape C.head a⟩ := ha
  rw [ha'] at he
  simpa only [compiledInput, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using he

theorem Steps.flow_nat {M : Alternating.Machine} {hM : M.WellFormed}
    {C D : Configuration (State M) (Alphabet M)} {n : ℕ}
    (h : Steps (finiteMachine M hM) n C D)
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow (compiledInput M hM).period
      (compiledInput M hM).realizingVelocity Φ) :
    Φ n (atHeight (codedPoint M C) (1 / 2)) = atHeight (codedPoint M D) (1 / 2) := by
  induction h with
  | zero C => simpa only [Nat.cast_zero] using hΦ.initial (atHeight (codedPoint M C) (1 / 2))
  | @next n C D E h hs ih =>
    rw [Nat.cast_add, Nat.cast_one, add_comm,
      hΦ.nat_shift (realizingVelocity_time_periodic _) n 1, ih]
    exact hs.flow_one hΦ

end ForcedComputation.Recorder

end

end OAI
