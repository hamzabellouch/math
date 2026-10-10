import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderLoader
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InitializedBundle

namespace OAI

/-! The initialized-computation main theorem of *Finite Instructions and
Solenoidal Shear Flows*. The machine-only body and input loader are explicit
finite rational data. -/

namespace ForcedComputation
open ShearFlows Recorder
open scoped ContDiff

noncomputable def machineVelocity (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Velocity :=
  initializedProgram (recorderLoader I hI) (compiledInput I.1 hI.1)

noncomputable def machineForce (ν : ℝ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Velocity := force ν (machineVelocity I hI)

/-- The compiler outputs two finite rational instruction tables. The body
is computed from the machine alone; only the one-period loader uses the input. -/
def machineProgram (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    Input × Input := (recorderLoader I hI, compiledInput I.1 hI.1)

theorem machineVelocity_tail (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {t : ℝ} (ht : 1 ≤ t) (x : Space) :
    machineVelocity I hI (t, x) = (compiledInput I.1 hI.1).realizingVelocity (t, x) :=
  initializedProgram_tail _ _ ht x

theorem machineForce_tail (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) {t : ℝ} (ht : 1 ≤ t) (x : Space) :
    machineForce ν I hI (t, x) = force ν (compiledInput I.1 hI.1).realizingVelocity (t, x) :=
  initializedForce_tail (recorderLoader_valid I hI) (compiledInput_valid I.1 hI.1) ν ht x

theorem initialized_computation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) (hν : 0 < ν) :
    InitializedFluidProperties 1 ν (machineVelocity I hI) ∧
    ∃ Φ : ℝ → Space → Space, IsMaterialFlow 1 (machineVelocity I hI) Φ ∧
      (Alternating.Halts I ↔ ∃ t : ℝ, 0 ≤ t ∧
        1 / 2 < Φ t ![1 / 8, 3 / 8, 1 / 2] 0 ∧ Φ t ![1 / 8, 3 / 8, 1 / 2] 0 < 1) := by
  let loader := recorderLoader I hI
  let body := compiledInput I.1 hI.1
  have hl : ValidInput loader := recorderLoader_valid I hI
  have hb : ValidInput body := compiledInput_valid I.1 hI.1
  have hp : loader.period = body.period := rfl
  have hp1 : (body.period : ℝ) = 1 := by
    change ((1 : ℚ) : ℝ) = 1
    norm_num
  have hproperties := initialized_bundle hl hb hp ν hν.le
  rw [hp1] at hproperties
  refine ⟨hproperties, ?_⟩
  obtain ⟨Φ, hΦ⟩ := initializedProgram_materialFlow hl hb hp
  obtain ⟨Ψ, hΨ⟩ := realizingVelocity_materialFlow hb
  obtain ⟨Λ, hΛ⟩ := realizingVelocity_materialFlow hl
  have hΛ' : IsMaterialFlow 1 loader.realizingVelocity Λ := by
    simpa only [loader, recorderLoader, loaderInput, Rat.cast_one] using hΛ
  have hbody := recorder_flow_halting_iff I hI 1 (by norm_num) hΨ
  rw [← initialPointQ_spec I hI] at hbody
  have hq : ¬Alternating.Halts I → (initialPointQ I hI 0 : ℝ) ≤ 1 / 3 := by
    intro hno
    have hc : recorderHalting I.1 (finiteInitializedRecorder I hI).control = false := by
      cases hh : recorderHalting I.1 (finiteInitializedRecorder I hI).control with
      | false => rfl
      | true =>
        apply False.elim
        apply hno
        apply (finite_recorder_halts_iff I hI).mp
        exact ⟨0, finiteInitializedRecorder I hI, initialState I.1, Steps.zero _, rfl, hh⟩
    have hB : (1 : ℝ) < radixBase I.1 := by exact_mod_cast radixBase_gt_one I.1
    have hd : ∀ a, (0 : ℝ) ≤ radixDigit I.1 a ∧
        (radixDigit I.1 a : ℝ) ≤ (radixBase I.1 : ℝ) - 1 := by
      intro a
      exact ⟨(radixDigit_bounds I.1 a).1, by linarith [(radixDigit_bounds I.1 a).2]⟩
    have he := Radix.encode_mem_unit hB hd (tapeAt (finiteInitializedRecorder I hI)).1
    have hκ : (0 : ℝ) < bandScale I.1 := by exact_mod_cast bandScale_pos I.1
    have hκ' : (bandScale I.1 : ℝ) ≤ 1 / 64 := by
      have h := (Rat.cast_le (K := ℝ)).mpr (bandScale_le I.1)
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
    rw [show (initialPointQ I hI 0 : ℝ) =
        codedPoint I.1 (finiteInitializedRecorder I hI) 0 from congrFun (initialPointQ_spec I hI) 0,
      codedPoint_first, hc]
    simp only [Bool.false_eq_true, ite_false]
    nlinarith [he.2]
  have hevent := initialized_observation_iff hl hb hΦ hΨ hΛ' hbody hq
  refine ⟨Φ, ?_, ?_⟩
  · change IsMaterialFlow 1 (initializedProgram loader body) Φ
    simpa only [hp1] using hΦ
  · simpa only [fixedStart, atHeight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hevent.symm

/-- The force is evaluated to every rational accuracy by the explicit finite
loader/body program, with an oracle only for the viscosity and query point. -/
theorem machineForce_effective (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) (α : List (Fin 4))
    {a : ℕ → ℚ} (ha : IsFastRealName a ν) {b : ℕ → RationalSpaceTime}
    {y : SpaceTime} (hb : IsFastName b y) (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (machineForce ν I hI) α y -
      rationalVector (evaluateInitializedForce (recorderLoader I hI) (compiledInput I.1 hI.1)
        (recorderLoader_valid I hI) (compiledInput_valid I.1 hI.1) α a b ε hε)‖ ≤ (ε : ℝ) :=
  evaluateInitializedForce_spec (recorderLoader_valid I hI) (compiledInput_valid I.1 hI.1)
    α ha hb ε hε

/-- The complete initialized main result, including the explicit evaluator
and the machine-only tail of both velocity and forcing. -/
theorem initialized_effective_computation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) (hν : 0 < ν) :
    InitializedFluidProperties 1 ν (machineVelocity I hI) ∧
    (∀ t x, 1 ≤ t →
      machineVelocity I hI (t, x) = (compiledInput I.1 hI.1).realizingVelocity (t, x) ∧
      machineForce ν I hI (t, x) = force ν (compiledInput I.1 hI.1).realizingVelocity (t, x)) ∧
    (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime) (y : SpaceTime),
      IsFastRealName a ν → IsFastName b y → ∀ (ε : ℚ) (hε : 0 < ε),
        ‖mixedDerivative (machineForce ν I hI) α y -
          rationalVector (evaluateInitializedForce (recorderLoader I hI) (compiledInput I.1 hI.1)
            (recorderLoader_valid I hI) (compiledInput_valid I.1 hI.1) α a b ε hε)‖ ≤ (ε : ℝ)) ∧
    ∃ Φ : ℝ → Space → Space, IsMaterialFlow 1 (machineVelocity I hI) Φ ∧
      (Alternating.Halts I ↔ ∃ t : ℝ, 0 ≤ t ∧
        1 / 2 < Φ t ![1 / 8, 3 / 8, 1 / 2] 0 ∧ Φ t ![1 / 8, 3 / 8, 1 / 2] 0 < 1) := by
  obtain ⟨hp, hf⟩ := initialized_computation I hI ν hν
  refine ⟨hp, fun t x ht => ⟨machineVelocity_tail I hI ht x,
    machineForce_tail I hI ν ht x⟩, ?_, hf⟩
  intro α a b y ha hb ε hε
  exact machineForce_effective I hI ν α ha hb ε hε

end ForcedComputation

end OAI
