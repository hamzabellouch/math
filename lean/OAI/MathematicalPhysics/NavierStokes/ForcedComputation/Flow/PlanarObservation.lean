import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NormalizedPlanarRouting
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarIteration

namespace OAI

/-! All-time observation of the actual planar processor. Nonhalting excludes
the entire continuous trajectory, while a halt is witnessed at an integer. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar
open ShearFlows Set Radix

theorem shifted_planar_observation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (δ : Fin 2 → ℚ) (hδ : |(δ 1 : ℝ)| ≤ 3 / 1024)
    {V : ℝ → Plane → Plane} {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition V Ψ) (hV : ∀ y, Function.Periodic (fun t => V t y) 1)
    (hone : ∀ {C D : Configuration (State I.1) (Alphabet I.1)},
      Step (finiteMachine I.1 hI.1) C D →
      Ψ 0 1 (shiftPoint δ (point I.1 hI.1 C)) = shiftPoint δ (point I.1 hI.1 D))
    (hsafe : ∀ {C D : Configuration (State I.1) (Alphabet I.1)},
      Step (finiteMachine I.1 hI.1) C D →
      recorderHalting I.1 C.control = false → recorderHalting I.1 D.control = false →
      ∀ s ∈ Icc (0 : ℝ) 1,
        3 / 16 ≤ Ψ 0 s (shiftPoint δ (point I.1 hI.1 C)) 1) :
    (∃ t : ℝ, 0 ≤ t ∧ Ψ 0 t
      (shiftPoint δ (point I.1 hI.1 (finiteInitializedRecorder I hI))) ∈ observer) ↔
      Alternating.Halts I := by
  let C₀ := finiteInitializedRecorder I hI
  let code : Configuration (State I.1) (Alphabet I.1) → Plane :=
    fun C => shiftPoint δ (point I.1 hI.1 C)
  constructor
  · rintro ⟨t, ht, hobs⟩
    by_contra hno
    have hn (n : ℕ) : (finiteMachine I.1 hI.1).halting
        (workAt (finiteMachine I.1 hI.1) (initialState I.1) (initialAlphabet I hI) n).state = false := by
      have he := congrArg WorkConfiguration.state (finite_workAt I hI n)
      change (workAt (finiteMachine I.1 hI.1) (initialState I.1)
        (initialAlphabet I hI) n).state.val = (Alternating.configurationAt I n).state at he
      change I.1.isHalting _ = false
      rw [he]
      cases hh : I.1.isHalting (Alternating.configurationAt I n).state with
      | false => rfl
      | true => exact False.elim (hno ⟨n, hh⟩)
    have hs (n : ℕ) : Steps (finiteMachine I.1 hI.1) n C₀
        (run (finiteMachine I.1 hI.1) C₀ n) :=
      run_steps_of_nonhalting _ _ _ 2 (by norm_num) hn n
    have hnext (n : ℕ) : Step (finiteMachine I.1 hI.1)
        (run (finiteMachine I.1 hI.1) C₀ n) (run (finiteMachine I.1 hI.1) C₀ (n + 1)) :=
      run_step_of_nonhalting _ _ _ 2 (by norm_num) hn n
    have hcontrol (n : ℕ) : recorderHalting I.1
        (run (finiteMachine I.1 hI.1) C₀ n).control = false := by
      obtain ⟨_, _, _, hr, _⟩ := hnext n
      have hh := hr.source_nonhalting
      have heq (q : Control (State I.1) (Alphabet I.1)) :
          haltingControl (finiteMachine I.1 hI.1) q = recorderHalting I.1 q := by
        cases q <;> rfl
      rwa [heq] at hh
    let n : ℕ := ⌊t⌋₊
    have hnt : (n : ℝ) ≤ t := Nat.floor_le ht
    have htn : t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
    have hseg := hsafe (hnext n) (hcontrol n) (hcontrol (n + 1))
      (t - (n : ℝ)) (show t - (n : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> linarith)
    have he := planar_recorder_steps hΨ hV code hone (hs n)
    have htime : t = (n : ℝ) + (t - (n : ℝ)) := by ring
    change 1 / 32 < Ψ 0 t (code C₀) 1 ∧ Ψ 0 t (code C₀) 1 < 1 / 8 at hobs
    rw [htime, hΨ.nat_shift hV, he] at hobs
    linarith [hobs.2]
  · intro hhalt
    obtain ⟨n, C, q, hs, hc, hh⟩ := (finite_recorder_halts_iff I hI).mpr hhalt
    have he := planar_recorder_steps hΨ hV code hone hs
    have hob := (shifted_point_observer_iff I.1 hI.1 C δ hδ).mpr
      (by simpa only [hc, recorderHalting] using hh)
    refine ⟨n, Nat.cast_nonneg _, ?_⟩
    change Ψ 0 n (code C₀) ∈ observer
    rw [he]
    exact hob

theorem normalized_planar_observation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ψ) :
    (∃ t : ℝ, 0 ≤ t ∧ Ψ 0 t ![1 / 4, 1 / 4] ∈ observer) ↔ Alternating.Halts I := by
  have hb := initialShift_small (freshInput I) (freshInput_valid hI)
    (fresh_initial_nonhalting I hI)
  have h := (shifted_planar_observation (freshInput I) (freshInput_valid hI)
    (initialShift (freshInput I) (freshInput_valid hI)) hb.2 hΨ
    (planarSlice_periodic (normalizedHamiltonian_periodic I hI))
    (normalized_planar_step I hI hΨ) (fun {C D} hstep _ hD s hs => by
      obtain ⟨b, _, ht, hx, _⟩ := step_branch hstep
      have hn : recorderHalting (freshMachine I.1) b.target = false := by rw [ht]; exact hD
      have hh := ((normalized_branch_planar_safe I hI b hn hx hΨ).2 s hs).2
      simpa [normalizedAnchors, branchAnchors_first, translatedPoint_eq_shiftPoint, horizontal] using hh)).trans
        (freshInput_halts_iff hI)
  rw [initialShift_spec] at h
  exact h

end ForcedComputation.Recorder.Planar

end

end OAI
