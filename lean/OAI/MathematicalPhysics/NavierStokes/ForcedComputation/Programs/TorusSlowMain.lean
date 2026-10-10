import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowLoaded
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowEffective
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowTail

namespace OAI

/-! The unit-torus slow-clock main theorem, at the fixed particle specified
in Scalar Potentials and Slow Clocks for Forced Fluid Computation. -/

namespace ForcedComputation
open ShearFlows Recorder

def torusSlowStart : Fin 2 → ℚ := ![1 / 4, 1 / 2]

def torusSlowProgram (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    Input × Input :=
  (shiftedLoader torusSlowStart (initialPointQ I hI) (1 / 2),
    recorderInputAtHeight I.1 hI.1 (1 / 2))

theorem torusSlowLoader_valid (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : ValidInput (torusSlowProgram I hI).1 :=
  shiftedLoader_valid _ _ _ (by intro j; fin_cases j <;> norm_num [torusSlowStart])
    (initialPointQ_bounds I hI)

theorem torusSlowBody_valid (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : ValidInput (torusSlowProgram I hI).2 :=
  recorderInputAtHeight_valid I.1 (Alternating.ValidInput.machine_wellFormed hI) (1 / 2)

noncomputable def torusSlowVelocity (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Velocity :=
  slowFromRest (loadedMachineVelocity torusSlowStart (1 / 2) I hI)

noncomputable def torusSlowForce (ν : ℝ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Velocity := force ν (torusSlowVelocity I hI)

theorem torus_slow_effective_computation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) (hν : 0 < ν) :
    SlowFluidProperties 1 ν (torusSlowVelocity I hI) ∧
    (∀ (β : List (Fin 3)) (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, 0 ≤ t →
      ‖iteratedDeriv n (fun s => spatialWord β (fun y => torusSlowVelocity I hI (s, y)) x) t‖ ≤
        C * (1 + t)⁻¹ ^ (1 + n) ∧
      ‖iteratedDeriv n (fun s => spatialWord β (fun y => torusSlowForce ν I hI (s, y)) x) t‖ ≤
        C * (1 + t)⁻¹ ^ (1 + n)) ∧
    (∀ t x, Real.exp 1 - 1 ≤ t →
      torusSlowVelocity I hI (t, x) =
        slowVelocity (recorderInputAtHeight I.1 hI.1 (1 / 2)).realizingVelocity (t, x) ∧
      torusSlowForce ν I hI (t, x) =
        force ν (slowVelocity (recorderInputAtHeight I.1 hI.1 (1 / 2)).realizingVelocity) (t, x)) ∧
    (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime) (y : SpaceTime)
      (ha : IsFastRealName a ν) (hb : IsFastName b y) (ε : ℚ) (hε : 0 < ε),
      ‖mixedDerivative (torusSlowForce ν I hI) α y -
        rationalVector (evaluateSlowForce (torusSlowProgram I hI).1
          (torusSlowProgram I hI).2 (torusSlowLoader_valid I hI)
          (torusSlowBody_valid I hI) α a ha b hb ε hε)‖ ≤ (ε : ℝ)) ∧
    ∃ Ψ : ℝ → Space → Space, IsMaterialFlow 1 (torusSlowVelocity I hI) Ψ ∧
      (Alternating.Halts I ↔ ∃ t : ℝ, 0 ≤ t ∧
        1 / 2 < Ψ t ![1 / 4, 1 / 2, 1 / 2] 0 ∧ Ψ t ![1 / 4, 1 / 2, 1 / 2] 0 < 1) := by
  obtain ⟨hp, Ψ, hΨ, hevent⟩ := slow_loaded_computation torusSlowStart (1 / 2)
    (by intro j; fin_cases j <;> norm_num [torusSlowStart])
    (by norm_num [torusSlowStart]) I hI ν hν
  refine ⟨hp, ?_, ?_, ?_, Ψ, hΨ, ?_⟩
  · intro β n
    let loader := (torusSlowProgram I hI).1
    let body := (torusSlowProgram I hI).2
    have hl : ValidInput loader := torusSlowLoader_valid I hI
    have hb : ValidInput body := torusSlowBody_valid I hI
    have hs := initializedProgram_smooth hl hb
    have hz : ∀ t, t < (1 / 32 : ℝ) → ∀ x, initializedProgram loader body (t, x) = 0 :=
      fun _ ht x => initializedProgram_zero_extend loader body ht x
    have hbounded := initializedProgram_bounded hl hb (show loader.period = body.period from rfl)
    obtain ⟨A, hA, hUA⟩ := slowFromRest_spatial_time_decay hs hz hbounded β n
    obtain ⟨B, hB, hFB⟩ := slowFromRest_force_spatial_time_decay hs hz hbounded
      (initializedProgram_zero_advection hl hb) ν β n
    refine ⟨A + B, add_nonneg hA hB, fun x t ht => ⟨?_, ?_⟩⟩
    · exact (hUA x t ht).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (by positivity))
    · exact (hFB x t ht).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (by positivity))
  · intro t x ht
    exact slow_initialized_tail _ _ ν ht x
  · intro α a b y ha hb ε hε
    exact evaluateSlowForce_spec (torusSlowLoader_valid I hI)
      (torusSlowBody_valid I hI) α a ha b hb ε hε
  · simpa only [torusSlowStart, atHeight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hevent

end ForcedComputation

end OAI
