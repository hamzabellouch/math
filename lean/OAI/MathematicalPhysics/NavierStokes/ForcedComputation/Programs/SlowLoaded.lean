import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LoadedMachine
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowBundle

namespace OAI

/-! The slowed computation works at every rational loading point and coding
height used by the fixed-label applications. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Recorder Set
open scoped ContDiff NNReal

theorem slow_loaded_computation (p : Fin 2 → ℚ) (z : ℚ)
    (hp : ∀ j, 1 / 8 ≤ p j ∧ p j ≤ 7 / 8) (hp0 : (p 0 : ℝ) ≤ 1 / 3)
    (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) (hν : 0 < ν) :
    SlowFluidProperties 1 ν (slowFromRest (loadedMachineVelocity p z I hI)) ∧
    ∃ Ψ : ℝ → Space → Space, IsMaterialFlow 1 (slowFromRest (loadedMachineVelocity p z I hI)) Ψ ∧
      (Alternating.Halts I ↔ ∃ t : ℝ, 0 ≤ t ∧
        1 / 2 < Ψ t (atHeight (fun j => (p j : ℝ)) z) 0 ∧ Ψ t (atHeight (fun j => (p j : ℝ)) z) 0 < 1) := by
  let loader := shiftedLoader p (initialPointQ I hI) z
  let body := recorderInputAtHeight I.1 hI.1 z
  let V := loadedMachineVelocity p z I hI
  have hl : ValidInput loader := shiftedLoader_valid _ _ _
    hp (initialPointQ_bounds I hI)
  have hb : ValidInput body := recorderInputAtHeight_valid _ _ _
  have hperiod : loader.period = body.period := rfl
  have hbodyPeriod : (body.period : ℝ) = 1 := recorderInputAtHeight_period _ _ _
  have hprops := slow_initialized_bundle hl hb hperiod ν hν.le
  rw [hbodyPeriod] at hprops
  refine ⟨hprops, ?_⟩
  obtain ⟨_, Φ, hΦ, hobs⟩ := loadedMachine_computation p z hp hp0 I hI ν hν
  obtain ⟨K, hK⟩ := initializedProgram_spatial_lipschitz hl hb
  have hs : ContDiff ℝ ∞ V := initializedProgram_smooth hl hb
  have hper : SpatiallyPeriodic 1 V := by
    change SpatiallyPeriodic 1 (initializedProgram loader body)
    simpa only [hbodyPeriod] using initializedProgram_periodic hperiod
  have hz : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0 :=
    fun _ ht x => initializedProgram_zero_extend loader body ht x
  obtain ⟨B, hB, hbound⟩ := initializedProgram_bounded hl hb hperiod []
  obtain ⟨Ψ, hΨ⟩ := slowFromRest_materialFlow hs hper hz hK hB hbound
  refine ⟨Ψ, hΨ, ?_⟩
  have he := slowFromRest_reaches_iff (fun x => hz 0 (by norm_num) x) hΦ hΨ hK
    (atHeight (fun j => (p j : ℝ)) z) {x : Space | 1 / 2 < x 0 ∧ x 0 < 1}
  simp only [Reaches, mem_ofPred_eq] at he
  have hevent := hobs.trans he.symm
  exact hevent


end ForcedComputation

end

end OAI
