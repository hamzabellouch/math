import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LoadedMachine
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowBundle

namespace OAI

/-! Analytic properties and the fixed-particle observation for the
square-integrable forcing construction. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Recorder Set
open scoped ContDiff NNReal

def fixedParticleVelocity (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : Velocity :=
  slowFromRest (loadedMachineVelocity fixedStart 0 I hI)

theorem fixed_particle_analytic_computation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) (hν : 0 < ν) :
    SlowFluidProperties 1 ν (fixedParticleVelocity I hI) ∧
    ∃ Ψ : ℝ → Space → Space, IsMaterialFlow 1 (fixedParticleVelocity I hI) Ψ ∧
      (Alternating.Halts I ↔ ∃ t : ℝ, 0 ≤ t ∧
        1 / 2 < Ψ t ![1 / 8, 3 / 8, 0] 0 ∧ Ψ t ![1 / 8, 3 / 8, 0] 0 < 1) := by
  let loader := shiftedLoader fixedStart (initialPointQ I hI) 0
  let body := recorderInputAtHeight I.1 hI.1 0
  let V := loadedMachineVelocity fixedStart 0 I hI
  have hl : ValidInput loader := shiftedLoader_valid _ _ _
    (by intro j; fin_cases j <;> norm_num [fixedStart]) (initialPointQ_bounds I hI)
  have hb : ValidInput body := recorderInputAtHeight_valid _ _ _
  have hp : loader.period = body.period := rfl
  have hbodyPeriod : (body.period : ℝ) = 1 := recorderInputAtHeight_period _ _ _
  have hprops := slow_initialized_bundle hl hb hp ν hν.le
  rw [hbodyPeriod] at hprops
  refine ⟨hprops, ?_⟩
  obtain ⟨_, Φ, hΦ, hobs⟩ := loadedMachine_computation fixedStart 0
    (by intro j; fin_cases j <;> norm_num [fixedStart]) (by norm_num [fixedStart]) I hI ν hν
  simp only [Rat.cast_zero] at hobs
  obtain ⟨K, hK⟩ := initializedProgram_spatial_lipschitz hl hb
  have hs : ContDiff ℝ ∞ V := initializedProgram_smooth hl hb
  have hper : SpatiallyPeriodic 1 V := by
    change SpatiallyPeriodic 1 (initializedProgram loader body)
    simpa only [hbodyPeriod] using initializedProgram_periodic hp
  have hz : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0 :=
    fun _ ht x => initializedProgram_zero_extend loader body ht x
  obtain ⟨B, hB, hbound⟩ := initializedProgram_bounded hl hb hp []
  obtain ⟨Ψ, hΨ⟩ := slowFromRest_materialFlow hs hper hz hK hB hbound
  refine ⟨Ψ, hΨ, ?_⟩
  have he := slowFromRest_reaches_iff (fun x => hz 0 (by norm_num) x) hΦ hΨ hK
    (atHeight (fun j => (fixedStart j : ℝ)) 0) {x : Space | 1 / 2 < x 0 ∧ x 0 < 1}
  simp only [Reaches, mem_ofPred_eq] at he
  have hevent := hobs.trans he.symm
  simpa only [Reaches, mem_ofPred_eq, fixedStart, atHeight,
    Matrix.cons_val_zero, Matrix.cons_val_one, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, Rat.cast_zero] using hevent

end ForcedComputation

end

end OAI
