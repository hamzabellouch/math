import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LoadedMachine

namespace OAI

/-! The initialized prefix-computation main theorem: the fixed label and
unit-torus observer are those in Prefix Instructions and Incompressible Flows.
The repeated table uses the machine alone, and the input appears only in the
finite rational loader. -/

namespace ForcedComputation
open ShearFlows Recorder

def prefixStart : Fin 2 → ℚ := ![1 / 8, 1 / 4]

def prefixProgram (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : Input × Input :=
  (shiftedLoader prefixStart (initialPointQ I hI) (1 / 4),
    recorderInputAtHeight I.1 hI.1 (1 / 4))

theorem prefixLoader_valid (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    ValidInput (prefixProgram I hI).1 :=
  shiftedLoader_valid _ _ _ (by intro j; fin_cases j <;> norm_num [prefixStart])
    (initialPointQ_bounds I hI)

theorem prefixBody_valid (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    ValidInput (prefixProgram I hI).2 :=
  recorderInputAtHeight_valid I.1 (Alternating.ValidInput.machine_wellFormed hI) (1 / 4)

noncomputable def prefixVelocity (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    Velocity := loadedMachineVelocity prefixStart (1 / 4) I hI

noncomputable def prefixForce (ν : ℝ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Velocity := force ν (prefixVelocity I hI)

/-- Full fixed-label main result, with the finite force evaluator and the
machine-only repeated velocity/force template exposed in its statement. -/
theorem prefix_effective_computation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) (hν : 0 < ν) :
    InitializedFluidProperties 1 ν (prefixVelocity I hI) ∧
    (∀ t x, 1 ≤ t →
      prefixVelocity I hI (t, x) = (recorderInputAtHeight I.1 hI.1 (1 / 4)).realizingVelocity (t, x) ∧
      prefixForce ν I hI (t, x) =
        force ν (recorderInputAtHeight I.1 hI.1 (1 / 4)).realizingVelocity (t, x)) ∧
    (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime) (y : SpaceTime),
      IsFastRealName a ν → IsFastName b y → ∀ (ε : ℚ) (hε : 0 < ε),
        ‖mixedDerivative (prefixForce ν I hI) α y -
          rationalVector (evaluateInitializedForce (prefixProgram I hI).1 (prefixProgram I hI).2
            (prefixLoader_valid I hI) (prefixBody_valid I hI) α a b ε hε)‖ ≤ (ε : ℝ)) ∧
    ∃ Φ : ℝ → Space → Space, IsMaterialFlow 1 (prefixVelocity I hI) Φ ∧
      (Alternating.Halts I ↔ ∃ t : ℝ, 0 ≤ t ∧
        1 / 2 < Φ t ![1 / 8, 1 / 4, 1 / 4] 0 ∧ Φ t ![1 / 8, 1 / 4, 1 / 4] 0 < 1) := by
  obtain ⟨hp, Φ, hΦ, hevent⟩ := loadedMachine_computation prefixStart (1 / 4)
    (by intro j; fin_cases j <;> norm_num [prefixStart]) (by norm_num [prefixStart]) I hI ν hν
  refine ⟨hp, ?_, ?_, Φ, hΦ, ?_⟩
  · intro t x ht
    exact ⟨initializedProgram_tail _ _ ht x,
      initializedForce_tail (prefixLoader_valid I hI) (prefixBody_valid I hI) ν ht x⟩
  · intro α a b y ha hb ε hε
    exact evaluateInitializedForce_spec (prefixLoader_valid I hI) (prefixBody_valid I hI)
      α ha hb ε hε
  · simpa only [prefixStart, atHeight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hevent

end ForcedComputation

end OAI
