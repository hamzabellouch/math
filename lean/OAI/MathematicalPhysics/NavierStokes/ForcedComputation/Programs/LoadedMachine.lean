import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ShiftedLoader
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderAtHeight
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InitializedBundle

namespace OAI

/-! Initialized computation at each paper's fixed rational particle label. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Recorder Set

theorem initialized_observation_atHeight {p q : Fin 2 → ℚ} {z : ℚ} {body : Input}
    (hl : ValidInput (shiftedLoader p q z)) (hb : ValidInput body)
    {Φ Ψ Λ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow body.period
      (initializedProgram (shiftedLoader p q z) body) Φ)
    (hΨ : IsMaterialFlow body.period body.realizingVelocity Ψ)
    (hΛ : IsMaterialFlow 1 (shiftedLoader p q z).realizingVelocity Λ)
    {H : Prop} {upper : ℝ}
    (hbody : (∃ t : ℝ, 0 ≤ t ∧
      1 / 2 < Ψ t (atHeight (fun j => (q j : ℝ)) (z : ℝ)) 0 ∧
      Ψ t (atHeight (fun j => (q j : ℝ)) (z : ℝ)) 0 < upper) ↔ H)
    (hp : (p 0 : ℝ) ≤ 1 / 3)
    (hq : ¬H → (q 0 : ℝ) ≤ 1 / 3) :
    (∃ t : ℝ, 0 ≤ t ∧
      1 / 2 < Φ t (atHeight (fun j => (p j : ℝ)) (z : ℝ)) 0 ∧
      Φ t (atHeight (fun j => (p j : ℝ)) (z : ℝ)) 0 < upper) ↔ H := by
  have hΛ' : IsMaterialFlow (shiftedLoader p q z).period
      (shiftedLoader p q z).realizingVelocity Λ := by
    simpa only [shiftedLoader_period] using hΛ
  have hload : Φ 1 (atHeight (fun j => (p j : ℝ)) (z : ℝ)) =
      atHeight (fun j => (q j : ℝ)) (z : ℝ) := by
    rw [initializedFlow_loading hl hb hΦ hΛ' _ (t := 1) (by norm_num)]
    simpa only [shiftedLoader_height] using shiftedLoader_endpoint hl hΛ
  constructor
  · rintro ⟨t, ht, hx, hy⟩
    by_cases hlate : 1 ≤ t
    · apply hbody.mp
      refine ⟨t - 1, by linarith, ?_⟩
      rw [initializedFlow_tail hl hb hΦ hΨ _ hlate, hload] at hx hy
      exact ⟨hx, hy⟩
    · by_contra hn
      have hΛbound := shiftedLoader_first_le hl hΛ
        (a := 1 / 3) hp (hq hn)
        (show t ∈ Icc (0 : ℝ) 1 from ⟨ht, (lt_of_not_ge hlate).le⟩)
      rw [initializedFlow_loading hl hb hΦ hΛ' _ ⟨ht, (lt_of_not_ge hlate).le⟩] at hx
      linarith
  · intro h
    obtain ⟨t, ht, hx, hy⟩ := hbody.mpr h
    refine ⟨t + 1, by linarith, ?_⟩
    rw [initializedFlow_tail hl hb hΦ hΨ _ (by linarith), hload]
    simpa only [add_sub_cancel_right] using And.intro hx hy


theorem initialPointQ_nonhalting (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    ¬Alternating.Halts I → (initialPointQ I hI 0 : ℝ) ≤ 1 / 3 := by
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

def loadedMachineVelocity (p : Fin 2 → ℚ) (z : ℚ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Velocity :=
  initializedProgram (shiftedLoader p (initialPointQ I hI) z)
    (recorderInputAtHeight I.1 hI.1 z)

theorem loadedMachine_computation (p : Fin 2 → ℚ) (z : ℚ)
    (hp : ∀ j, 1 / 8 ≤ p j ∧ p j ≤ 7 / 8) (hp0 : (p 0 : ℝ) ≤ 1 / 3)
    (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (ν : ℝ) (hν : 0 < ν) :
    InitializedFluidProperties 1 ν (loadedMachineVelocity p z I hI) ∧
    ∃ Φ : ℝ → Space → Space, IsMaterialFlow 1 (loadedMachineVelocity p z I hI) Φ ∧
      (Alternating.Halts I ↔ ∃ t : ℝ, 0 ≤ t ∧
        1 / 2 < Φ t (atHeight (fun j => (p j : ℝ)) z) 0 ∧
        Φ t (atHeight (fun j => (p j : ℝ)) z) 0 < 1) := by
  let loader := shiftedLoader p (initialPointQ I hI) z
  let body := recorderInputAtHeight I.1 hI.1 z
  have hl : ValidInput loader := shiftedLoader_valid p _ z hp (initialPointQ_bounds I hI)
  have hb : ValidInput body := recorderInputAtHeight_valid I.1 hI.1 z
  have hperiod : loader.period = body.period := rfl
  have hp1 : (body.period : ℝ) = 1 := recorderInputAtHeight_period I.1 hI.1 z
  have hproperties := initialized_bundle hl hb hperiod ν hν.le
  rw [hp1] at hproperties
  refine ⟨hproperties, ?_⟩
  obtain ⟨Φ, hΦ⟩ := initializedProgram_materialFlow hl hb hperiod
  obtain ⟨Ψ, hΨ⟩ := realizingVelocity_materialFlow hb
  obtain ⟨Λ, hΛ⟩ := realizingVelocity_materialFlow hl
  have hΛ' : IsMaterialFlow 1 loader.realizingVelocity Λ := by
    simpa only [loader, shiftedLoader_period] using hΛ
  have hbody := recorder_flow_halting_iff_atHeight z I hI 1 (by norm_num) hΨ
  rw [← initialPointQ_spec I hI] at hbody
  have hevent := initialized_observation_atHeight hl hb hΦ hΨ hΛ' hbody hp0
    (initialPointQ_nonhalting I hI)
  refine ⟨Φ, ?_, hevent.symm⟩
  change IsMaterialFlow 1 (initializedProgram loader body) Φ
  simpa only [hp1] using hΦ

end ForcedComputation

end

end OAI
