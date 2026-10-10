import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SuspensionIteration
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarInitialShift

namespace OAI

/-! The observation argument for the autonomous suspension. The finite
processor supplies one-period branch trajectories, whose all-time
consequence is proved for the actual material flow. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set Radix

def stationaryObserver : Set Space :=
  letI := ShearFlows.neZeroThree
  letI := ShearFlows.thirtyTwoAtLeastTwo
  letI := ShearFlows.eightAtLeastTwo
  {x | 1 / 32 < x 1 ∧ x 1 < 1 / 8}

def stationaryStartingPoint : Space :=
  letI := ShearFlows.fourAtLeastTwo
  ![1 / 4, 1 / 4, 0]

namespace Recorder.Planar

theorem shifted_suspension_observation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (δ : Fin 2 → ℚ) (hδ : |(δ 1 : ℝ)| ≤ 3 / 1024)
    {W : Space → Space} {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y => W y.2) Φ)
    (hone : ∀ {C D : Configuration (State I.1) (Alphabet I.1)},
      Step (finiteMachine I.1 hI.1) C D →
      Φ 1 (atHeight (shiftPoint δ (point I.1 hI.1 C)) 0) =
        atHeight (shiftPoint δ (point I.1 hI.1 D)) 1)
    (hsafe : ∀ {C D : Configuration (State I.1) (Alphabet I.1)},
      Step (finiteMachine I.1 hI.1) C D →
      recorderHalting I.1 C.control = false → recorderHalting I.1 D.control = false →
      ∀ s ∈ Icc (0 : ℝ) 1,
        3 / 16 ≤ Φ s (atHeight (shiftPoint δ (point I.1 hI.1 C)) 0) 1) :
    Reaches (fun t => Φ t
      (atHeight (shiftPoint δ (point I.1 hI.1 (finiteInitializedRecorder I hI))) 0))
      stationaryObserver ↔ Alternating.Halts I := by
  let C₀ := finiteInitializedRecorder I hI
  let code : Configuration (State I.1) (Alphabet I.1) → Plane :=
    fun C => shiftPoint δ (point I.1 hI.1 C)
  have hperiod : TimePeriodic (fun y => W y.2) := fun _ _ => rfl
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
    have he := suspension_recorder_steps hΦ code hone (hs n)
    have hlift : atHeight (code (run (finiteMachine I.1 hI.1) C₀ n)) (n : ℝ) =
        atHeight (code (run (finiteMachine I.1 hI.1) C₀ n)) 0 +
          latticeVector 1 (verticalInteger (n : ℤ)) := by
      simpa only [Int.cast_natCast, zero_add] using
        atHeight_add_verticalInteger (code (run (finiteMachine I.1 hI.1) C₀ n)) 0 (n : ℤ)
    have htime : t = (t - (n : ℝ)) + (n : ℝ) := by ring
    change 1 / 32 < Φ t (atHeight (code C₀) 0) 1 ∧
      Φ t (atHeight (code C₀) 0) 1 < 1 / 8 at hobs
    rw [htime, hΦ.nat_shift hperiod n, he, hlift, hΦ.equivariant] at hobs
    have hv : latticeVector 1 (verticalInteger (n : ℤ)) 1 = 0 := by
      simp [latticeVector, verticalInteger]
    simp only [Pi.add_apply, hv, add_zero] at hobs
    linarith [hobs.2]
  · intro hhalt
    obtain ⟨n, C, q, hs, hc, hh⟩ := (finite_recorder_halts_iff I hI).mpr hhalt
    have he := suspension_recorder_steps hΦ code hone hs
    have hob := (shifted_point_observer_iff I.1 hI.1 C δ hδ).mpr
      (by simpa only [hc, recorderHalting] using hh)
    refine ⟨n, Nat.cast_nonneg _, ?_⟩
    change Φ n (atHeight (code C₀) 0) ∈ stationaryObserver
    rw [he]
    exact hob

theorem normalized_suspension_observation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {W : Space → Space} {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y => W y.2) Φ)
    (hone : ∀ {C D : Configuration (State (freshMachine I.1)) (Alphabet (freshMachine I.1))},
      Step (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) C D →
      Φ 1 (atHeight (shiftPoint (initialShift (freshInput I) (freshInput_valid hI))
        (point (freshMachine I.1) (freshInput_valid hI).1 C)) 0) =
      atHeight (shiftPoint (initialShift (freshInput I) (freshInput_valid hI))
        (point (freshMachine I.1) (freshInput_valid hI).1 D)) 1)
    (hsafe : ∀ {C D : Configuration (State (freshMachine I.1)) (Alphabet (freshMachine I.1))},
      Step (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) C D →
      recorderHalting (freshMachine I.1) C.control = false →
      recorderHalting (freshMachine I.1) D.control = false → ∀ s ∈ Icc (0 : ℝ) 1,
      3 / 16 ≤ Φ s (atHeight (shiftPoint (initialShift (freshInput I) (freshInput_valid hI))
        (point (freshMachine I.1) (freshInput_valid hI).1 C)) 0) 1) :
    Reaches (fun t => Φ t stationaryStartingPoint) stationaryObserver ↔ Alternating.Halts I := by
  have hb := initialShift_small (freshInput I) (freshInput_valid hI)
    (fresh_initial_nonhalting I hI)
  have h := (shifted_suspension_observation (freshInput I) (freshInput_valid hI)
    (initialShift (freshInput I) (freshInput_valid hI)) hb.2 hΦ hone hsafe).trans
      (freshInput_halts_iff hI)
  rw [initialShift_spec] at h
  exact h

end Recorder.Planar
end ForcedComputation

end

end OAI
