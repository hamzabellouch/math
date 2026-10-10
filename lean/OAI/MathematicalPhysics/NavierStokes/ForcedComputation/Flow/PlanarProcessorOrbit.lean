import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarObservation

namespace OAI

/-! The full orbit clauses for the planar processor: every simulated step,
the common corridor, nonhalting safety, and an integer-time halting margin. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar

open ShearFlows Set Radix

def normalizedPoint (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (C : Configuration (State (freshMachine I.1)) (Alphabet (freshMachine I.1))) : Plane :=
  shiftPoint (initialShift (freshInput I) (freshInput_valid hI))
    (point (freshMachine I.1) (freshInput_wellFormed hI) C)

def normalizedInitial (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :=
  finiteInitializedRecorder (freshInput I) (freshInput_valid hI)

theorem normalizedPoint_initial (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    normalizedPoint I hI (normalizedInitial I hI) = ![1 / 4, 1 / 4] :=
  initialShift_spec (freshInput I) (freshInput_valid hI)

theorem normalized_steps_realized (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ψ)
    {n : ℕ} {C D : Configuration (State (freshMachine I.1)) (Alphabet (freshMachine I.1))}
    (hs : Steps (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) n C D) :
    Ψ 0 n (normalizedPoint I hI C) = normalizedPoint I hI D :=
  planar_recorder_steps hΨ (planarSlice_periodic (normalizedHamiltonian_periodic I hI))
    (normalizedPoint I hI) (normalized_planar_step I hI hΨ) hs

theorem normalized_step_corridor (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ψ)
    {C D : Configuration (State (freshMachine I.1)) (Alphabet (freshMachine I.1))}
    (hs : Step (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) C D)
    {s : ℝ} (hs' : s ∈ Icc (0 : ℝ) 1) :
    Ψ 0 s (normalizedPoint I hI C) ∈ clockRectangle.carrier := by
  obtain ⟨b, _, _, hx, _⟩ := step_branch hs
  have h := (normalized_branch_planar I hI b hx hΨ).2 s hs'
  simpa only [normalizedAnchors, branchAnchors_first, normalizedPoint,
    translatedPoint_eq_shiftPoint] using h

theorem normalized_step_safe (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ψ)
    {C D : Configuration (State (freshMachine I.1)) (Alphabet (freshMachine I.1))}
    (hs : Step (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) C D)
    (hD : recorderHalting (freshMachine I.1) D.control = false)
    {s : ℝ} (hs' : s ∈ Icc (0 : ℝ) 1) :
    3 / 16 ≤ Ψ 0 s (normalizedPoint I hI C) 1 := by
  obtain ⟨b, _, ht, hx, _⟩ := step_branch hs
  have hn : recorderHalting (freshMachine I.1) b.target = false := by rw [ht]; exact hD
  have h := ((normalized_branch_planar_safe I hI b hn hx hΨ).2 s hs').2
  simpa only [normalizedAnchors, branchAnchors_first, normalizedPoint,
    translatedPoint_eq_shiftPoint] using h

theorem finite_work_nonhalting (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (hno : ¬ Alternating.Halts I) (n : ℕ) :
    (finiteMachine I.1 hI.1).halting
      (workAt (finiteMachine I.1 hI.1) (initialState I.1) (initialAlphabet I hI) n).state = false := by
  have he := congrArg WorkConfiguration.state (finite_workAt I hI n)
  change (workAt (finiteMachine I.1 hI.1) (initialState I.1)
    (initialAlphabet I hI) n).state.val = (Alternating.configurationAt I n).state at he
  change I.1.isHalting _ = false
  rw [he]
  cases hh : I.1.isHalting (Alternating.configurationAt I n).state with
  | false => rfl
  | true => exact False.elim (hno ⟨n, hh⟩)

theorem normalized_nonhalting_corridor (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ψ)
    (hno : ¬ Alternating.Halts I) {t : ℝ} (ht : 0 ≤ t) :
    Ψ 0 t ![1 / 4, 1 / 4] ∈ clockRectangle.carrier ∧
      3 / 16 ≤ Ψ 0 t ![1 / 4, 1 / 4] 1 := by
  let J := freshInput I
  have hJ : Alternating.ValidInput J := freshInput_valid hI
  have hnoJ : ¬ Alternating.Halts J := fun hh => hno ((freshInput_halts_iff hI).mp hh)
  let C₀ := normalizedInitial I hI
  have hn := finite_work_nonhalting J hJ hnoJ
  have hsteps (n : ℕ) : Steps (finiteMachine J.1 hJ.1) n C₀
      (run (finiteMachine J.1 hJ.1) C₀ n) :=
    run_steps_of_nonhalting _ _ _ 2 (by norm_num) hn n
  have hnext (n : ℕ) : Step (finiteMachine J.1 hJ.1)
      (run (finiteMachine J.1 hJ.1) C₀ n) (run (finiteMachine J.1 hJ.1) C₀ (n + 1)) :=
    run_step_of_nonhalting _ _ _ 2 (by norm_num) hn n
  have hcontrol (n : ℕ) : recorderHalting J.1
      (run (finiteMachine J.1 hJ.1) C₀ n).control = false := by
    obtain ⟨_, _, _, hr, _⟩ := hnext n
    have hh := hr.source_nonhalting
    have heq (q : Control (State J.1) (Alphabet J.1)) :
        haltingControl (finiteMachine J.1 hJ.1) q = recorderHalting J.1 q := by
      cases q <;> rfl
    rwa [heq] at hh
  let n : ℕ := ⌊t⌋₊
  have hnt : (n : ℝ) ≤ t := Nat.floor_le ht
  have htn : t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
  have hs : t - (n : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith
  have htime : t = (n : ℝ) + (t - (n : ℝ)) := by ring
  rw [htime, hΨ.nat_shift (planarSlice_periodic (normalizedHamiltonian_periodic I hI)),
    ← normalizedPoint_initial I hI, normalized_steps_realized I hI hΨ (hsteps n)]
  exact ⟨normalized_step_corridor I hI hΨ (hnext n) hs,
    normalized_step_safe I hI hΨ (hnext n) (hcontrol (n + 1)) hs⟩

theorem normalized_halting_clearance (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ψ)
    (hh : Alternating.Halts I) :
    ∃ n : ℕ, 1 / 16 ≤ Ψ 0 n ![1 / 4, 1 / 4] 1 ∧
      Ψ 0 n ![1 / 4, 1 / 4] 1 ≤ 3 / 32 := by
  have hhJ := (freshInput_halts_iff hI).mpr hh
  obtain ⟨n, C, q, hs, hc, hhalt⟩ :=
    (finite_recorder_halts_iff (freshInput I) (freshInput_valid hI)).mpr hhJ
  have he := normalized_steps_realized I hI hΨ hs
  change Ψ 0 (n : ℝ) (normalizedPoint I hI (normalizedInitial I hI)) =
    normalizedPoint I hI C at he
  rw [normalizedPoint_initial I hI] at he
  have hq : recorderHalting (freshMachine I.1) C.control = true := by
    rw [hc]
    exact hhalt
  have hd := (initialShift_small (freshInput I) (freshInput_valid hI)
    (fresh_initial_nonhalting I hI)).2
  refine ⟨n, ?_⟩
  rw [he]
  exact shifted_halting_clearance _ _ C _ hq hd

end ForcedComputation.Recorder.Planar

end

end OAI
