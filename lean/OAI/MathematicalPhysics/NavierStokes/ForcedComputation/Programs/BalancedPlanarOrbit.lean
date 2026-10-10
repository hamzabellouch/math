import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedPlanarProgram

namespace OAI

/-! The same machine-only body processes every input point. Quantitative
orbit bounds make the all-time cube guard independent of the choice of
compact vertical cutoff. -/

noncomputable section
namespace ForcedComputation.BalancedPlanar
open ShearFlows Recorder Recorder.Planar Set

/-- The input point is rational and can be used as the loading target. -/
def inputPosition (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : Fin 2 → ℚ :=
  fun j => initialPoint (freshInput I) (freshInput_valid hI) j + referenceShift I.1 hI.1 j

theorem inputCode_rational (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    inputCode I hI = fun j => (inputPosition I hI j : ℝ) := by
  change shiftPoint (referenceShift I.1 hI.1)
      (point (freshInput I).1 (freshInput_valid hI).1
        (finiteInitializedRecorder (freshInput I) (freshInput_valid hI))) = _
  rw [← initialPoint_spec (freshInput I) (freshInput_valid hI)]
  funext j
  simp only [shiftPoint, inputPosition, Rat.cast_add]

theorem inputCode_bounds (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    |inputCode I hI 0 - 1 / 4| ≤ 1 / 256 ∧
      |inputCode I hI 1 - 1 / 4| ≤ 3 / 512 := by
  have hr := referenceShift_small I.1 hI.1
  have hi := initialShift_small (freshInput I) (freshInput_valid hI)
    (fresh_initial_nonhalting I hI)
  have he (j : Fin 2) : inputCode I hI j - 1 / 4 =
      (referenceShift I.1 hI.1 j : ℝ) -
        (initialShift (freshInput I) (freshInput_valid hI) j : ℝ) := by
    rw [inputCode_rational]
    simp only [inputPosition, initialShift, Rat.cast_add, Rat.cast_sub, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat]
    ring
  constructor
  · rw [he]
    exact (abs_sub _ _).trans (by linarith [hr.1, hi.1])
  · rw [he]
    exact (abs_sub _ _).trans (by linarith [hr.2, hi.2])

theorem inputCode_in_unit (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    ∀ j : Fin 2, 0 < inputCode I hI j ∧ inputCode I hI j < 1 := by
  have h := inputCode_bounds I hI
  intro j
  fin_cases j
  · change 0 < inputCode I hI 0 ∧ inputCode I hI 0 < 1
    obtain ⟨hl, hu⟩ := abs_le.mp h.1
    constructor <;> linarith
  · change 0 < inputCode I hI 1 ∧ inputCode I hI 1 < 1
    obtain ⟨hl, hu⟩ := abs_le.mp h.2
    constructor <;> linarith

theorem inputCode_loader_guard (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    4 ≤ inputCode I hI 0 + 16 * inputCode I hI 1 := by
  have h := inputCode_bounds I hI
  obtain ⟨hl, _⟩ := abs_le.mp h.1
  obtain ⟨hy, _⟩ := abs_le.mp h.2
  linarith

theorem body_periodic (M : Alternating.Machine) (hM : M.WellFormed) (x : Plane) :
    Function.Periodic (fun t => planarSlice (bodyHamiltonian M hM) t x) 1 :=
  planarSlice_periodic (normalizedHamiltonian_periodic (referenceInput M) (referenceValid hM)) x

theorem body_nonhalting_corridor (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (bodyHamiltonian I.1 hI.1)) Ψ)
    (hno : ¬ Alternating.Halts I) {t : ℝ} (ht : 0 ≤ t) :
    Ψ 0 t (inputCode I hI) ∈ clockRectangle.carrier ∧
      3 / 16 ≤ Ψ 0 t (inputCode I hI) 1 := by
  let J := freshInput I
  have hJ : Alternating.ValidInput J := freshInput_valid hI
  have hnoJ : ¬ Alternating.Halts J := fun hh => hno ((freshInput_halts_iff hI).mp hh)
  let C₀ := finiteInitializedRecorder J hJ
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
  have he := planar_recorder_steps hΨ (body_periodic I.1 hI.1)
    (bodyCode I.1 hI.1) (body_step I.1 hI.1 hΨ) (hsteps n)
  have htime : t = (n : ℝ) + (t - (n : ℝ)) := by ring
  have hpath : Ψ 0 t (inputCode I hI) =
      Ψ 0 (t - (n : ℝ)) (bodyCode I.1 hI.1 (run (finiteMachine J.1 hJ.1) C₀ n)) := by
    change Ψ 0 t (bodyCode I.1 hI.1 C₀) = _
    conv_lhs => rw [htime, hΨ.nat_shift (body_periodic I.1 hI.1), he]
  rw [hpath]
  exact ⟨body_step_corridor I.1 hI.1 hΨ (hnext n) hs,
    body_step_safe I.1 hI.1 hΨ (hnext n) (hcontrol (n + 1)) hs⟩

theorem body_halting_clearance (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (planarSlice (bodyHamiltonian I.1 hI.1)) Ψ)
    (hh : Alternating.Halts I) :
    ∃ n : ℕ, (0 < Ψ 0 n (inputCode I hI) 0 ∧ Ψ 0 n (inputCode I hI) 0 < 1) ∧
      1 / 16 ≤ Ψ 0 n (inputCode I hI) 1 ∧ Ψ 0 n (inputCode I hI) 1 ≤ 3 / 32 := by
  obtain ⟨n, C, q, hs, hc, hhalt⟩ :=
    (finite_recorder_halts_iff (freshInput I) (freshInput_valid hI)).mpr
      ((freshInput_halts_iff hI).mpr hh)
  have he := planar_recorder_steps hΨ (body_periodic I.1 hI.1)
    (bodyCode I.1 hI.1) (body_step I.1 hI.1 hΨ) hs
  have hq : recorderHalting (freshMachine I.1) C.control = true := by
    rw [hc]
    exact hhalt
  have hd := referenceShift_small I.1 hI.1
  have hy := shifted_halting_clearance (freshMachine I.1) (freshInput_valid hI).1 C
    (referenceShift I.1 hI.1) hq hd.2
  have hx := point_horizontal_bound (freshMachine I.1) (freshInput_valid hI).1 C
  have hk := compression_le_real (freshMachine I.1) (freshInput_valid hI).1
  obtain ⟨hxl, hxu⟩ := abs_le.mp hx
  obtain ⟨hdl, hdu⟩ := abs_le.mp hd.1
  refine ⟨n, ?_⟩
  have he' : Ψ 0 n (inputCode I hI) = bodyCode I.1 hI.1 C := he
  rw [he']
  change (0 < shiftPoint _ _ 0 ∧ shiftPoint _ _ 0 < 1) ∧
    1 / 16 ≤ shiftPoint _ _ 1 ∧ shiftPoint _ _ 1 ≤ 3 / 32
  refine ⟨?_, hy⟩
  change 0 < point (freshMachine I.1) (freshInput_valid hI).1 C 0 +
      (referenceShift I.1 hI.1 0 : ℝ) ∧
    point (freshMachine I.1) (freshInput_valid hI).1 C 0 +
      (referenceShift I.1 hI.1 0 : ℝ) < 1
  constructor <;> linarith

end ForcedComputation.BalancedPlanar

end

end OAI
