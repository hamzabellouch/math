import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicLoaderFlow

namespace OAI

/-! The fixed observer for the program which includes its loader in every
period. The fresh initial machine state makes every later loading row inert. -/

noncomputable section
namespace ForcedComputation.Recorder
open ShearFlows Radix Set

theorem periodic_flow_halting_iff (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow (periodicInitializedInput I hI).period
      (periodicInitializedInput I hI).realizingVelocity Φ) :
    (∃ t : ℝ, 0 ≤ t ∧ 1 / 2 < Φ t periodicStartingPoint 0 ∧
      Φ t periodicStartingPoint 0 < 7 / 8) ↔ Alternating.Halts I := by
  let J := freshInput I
  let hv := freshInput_valid hI
  let C₀ := finiteInitializedRecorder J hv
  rw [← freshInput_halts_iff hI]
  constructor
  · rintro ⟨t, ht, hx, _⟩
    by_contra hno
    by_cases ht1 : t ≤ 1
    · have hh := periodicLoading_safe I hI hΦ ⟨ht, ht1⟩
      linarith
    have hn (n : ℕ) : (finiteMachine J.1 hv.1).halting
        (workAt (finiteMachine J.1 hv.1) (initialState J.1)
          (initialAlphabet J hv) n).state = false := by
      have he := congrArg WorkConfiguration.state (finite_workAt J hv n)
      change (workAt (finiteMachine J.1 hv.1) (initialState J.1)
        (initialAlphabet J hv) n).state.val = (Alternating.configurationAt J n).state at he
      change J.1.isHalting _ = false
      rw [he]
      cases hh : J.1.isHalting (Alternating.configurationAt J n).state with
      | false => rfl
      | true => exact False.elim (hno ⟨n, hh⟩)
    have hs (n : ℕ) : Steps (finiteMachine J.1 hv.1) n C₀
        (run (finiteMachine J.1 hv.1) C₀ n) :=
      run_steps_of_nonhalting _ _ _ 2 (by norm_num) hn n
    have hnext (n : ℕ) : Step (finiteMachine J.1 hv.1)
        (run (finiteMachine J.1 hv.1) C₀ n)
        (run (finiteMachine J.1 hv.1) C₀ (n + 1)) :=
      run_step_of_nonhalting _ _ _ 2 (by norm_num) hn n
    have hcontrol (n : ℕ) : recorderHalting J.1
        (run (finiteMachine J.1 hv.1) C₀ n).control = false := by
      obtain ⟨_, _, _, hr, _⟩ := hnext n
      have hh := hr.source_nonhalting
      have heq (q : Control (State J.1) (Alphabet J.1)) :
          haltingControl (finiteMachine J.1 hv.1) q = recorderHalting J.1 q := by
        cases q <;> rfl
      rwa [heq] at hh
    let n : ℕ := ⌊t - 1⌋₊
    have hnt : (n : ℝ) ≤ t - 1 := Nat.floor_le (by linarith)
    have htn : t - 1 < (n : ℝ) + 1 := Nat.lt_floor_add_one (t - 1)
    have hsafe := (hnext n).flow_safe_in (hcontrol n) (hcontrol (n + 1))
      (periodicInitializedInput_valid I hI)
      (show ((periodicInitializedInput I hI).h : ℝ) ≤ (bandScale J.1 : ℝ) / 2 by
        simp [periodicInitializedInput, Input.shiftHeight, periodicLoadedInput, loadedInput,
          Input.withInstructions, compiledInput, J])
      (fun b hb _ _ => periodicLoadedInput_used_mem I hI (hs n) b hb) hΦ
      (show t - ((n : ℝ) + 1) ∈ Icc (0 : ℝ) 1 by constructor <;> linarith)
    have he := (hs n).flow_loaded hΦ
    have htime : t = (t - ((n : ℝ) + 1)) + ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [htime, hΦ.nat_shift (realizingVelocity_time_periodic _) (n + 1)] at hx
    have he' : Φ (n + 1 : ℕ) periodicStartingPoint =
        atHeight (codedPoint J.1 (run (finiteMachine J.1 hv.1) C₀ n))
          (periodicInitializedInput I hI).codingHeight := by simpa using he
    rw [he'] at hx
    linarith [hsafe.2]
  · intro hhalt
    obtain ⟨n, C, q, hs, hc, hh⟩ := (finite_recorder_halts_iff J hv).mpr hhalt
    have he := hs.flow_loaded hΦ
    have hob := (codedPoint_observation_iff J.1 C).mpr
      (by simpa only [hc, recorderHalting] using hh)
    refine ⟨n + 1, by positivity, ?_⟩
    rw [he]
    exact hob

end ForcedComputation.Recorder

end

end OAI
