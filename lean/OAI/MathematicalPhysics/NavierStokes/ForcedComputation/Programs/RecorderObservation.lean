import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderFlow
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderExecution
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ObservationByInstruction

namespace OAI

/-! Continuous-time observation of the genuine recorder orbit. Safe steps remain
inside the nonterminal strip throughout all seven shear stages. -/

noncomputable section
namespace ForcedComputation.Recorder
open ShearFlows Radix Set

theorem codedPoint_first (M : Alternating.Machine)
    (C : Configuration (State M) (Alphabet M)) :
    codedPoint M C 0 = (if recorderHalting M C.control then (3 / 4 : ℝ) else 1 / 4) +
      (bandScale M : ℝ) *
        (encode (radixBase M) (fun a => (radixDigit M a : ℝ)) (tapeAt C).1 - 1 / 2) := by
  cases hh : recorderHalting M C.control <;>
    simp only [codedPoint, configurationPoint, embedPlane, stateOffset, planeOfPair, coordinates,
      Matrix.cons_val_zero, hh, Bool.false_eq_true, ite_false, ite_true,
      Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] <;> ring


theorem codedPoint_observation_iff (M : Alternating.Machine)
    (C : Configuration (State M) (Alphabet M)) :
    (1 / 2 < codedPoint M C 0 ∧ codedPoint M C 0 < 7 / 8) ↔
      recorderHalting M C.control = true := by
  have hB : (1 : ℝ) < radixBase M := by exact_mod_cast radixBase_gt_one M
  have hdigits : ∀ a, (0 : ℝ) ≤ radixDigit M a ∧
      (radixDigit M a : ℝ) ≤ (radixBase M : ℝ) - 1 := by
    intro a
    exact ⟨(radixDigit_bounds M a).1, by linarith [(radixDigit_bounds M a).2]⟩
  have he := encode_mem_unit hB hdigits (tapeAt C).1
  have hκ : (0 : ℝ) < bandScale M := by exact_mod_cast bandScale_pos M
  have hκ' : (bandScale M : ℝ) ≤ 1 / 64 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (bandScale_le M)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  have hl : -(bandScale M : ℝ) / 2 ≤ (bandScale M : ℝ) *
      (encode (radixBase M) (fun a => (radixDigit M a : ℝ)) (tapeAt C).1 - 1 / 2) := by
    nlinarith [he.1]
  have hu : (bandScale M : ℝ) *
      (encode (radixBase M) (fun a => (radixDigit M a : ℝ)) (tapeAt C).1 - 1 / 2) ≤
        (bandScale M : ℝ) / 2 := by nlinarith [he.2]
  rw [codedPoint_first]
  cases hh : recorderHalting M C.control <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · constructor
    · intro h
      linarith [h.1]
    · exact False.elim
  · constructor
    · intro _
      trivial
    · intro _
      constructor <;> linarith

theorem Step.flow_safe {M : Alternating.Machine} {hM : M.WellFormed}
    {C D : Configuration (State M) (Alphabet M)}
    (h : Step (finiteMachine M hM) C D)
    (hc : recorderHalting M C.control = false) (hd : recorderHalting M D.control = false)
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow (compiledInput M hM).period
      (compiledInput M hM).realizingVelocity Φ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < Φ t (atHeight (codedPoint M C) (1 / 2)) 0 ∧
      Φ t (atHeight (codedPoint M C) (1 / 2)) 0 < 1 / 2 := by
  obtain ⟨q, a, d, hl, rfl⟩ := h
  let b : Branch (finiteMachine M hM) :=
    ⟨C.control, C.tape C.head, q, a, d, C.tape (C.head - 1), hl⟩
  have hv := compiledInput_valid M hM
  have hdigits : ∀ a, 0 ≤ radixDigit M a ∧ radixDigit M a ≤ radixBase M - 1 := by
    intro a
    exact ⟨(radixDigit_bounds_rat M a).1, by linarith [(radixDigit_bounds_rat M a).2]⟩
  have hx : codedPoint M C ∈ (geometricInstruction M hM b).source.carrier :=
    branchInstruction_contains (radixBase_gt_one M) hdigits (bandScale_pos M).le
      (stateOffset M) b C rfl rfl rfl
  have hs := stateBox_nonterminal_x M b.source hc (geometricInstruction_source_unit M hM b)
    (center_mem (geometricInstruction_source_positive M hM b))
  have hq := stateBox_nonterminal_x M b.target hd (geometricInstruction_target_unit M hM b)
    (center_mem (geometricInstruction_target_positive M hM b))
  have hlow := materialFlow_first_ge_of_mem hv hΦ (geometricInstruction_mem M hM b) hx
    (a := 1 / 4 - (bandScale M : ℝ) / 2) hs.1 hq.1 ht
  have hhigh := materialFlow_first_le_of_mem hv hΦ (geometricInstruction_mem M hM b) hx
    (a := 1 / 4 + (bandScale M : ℝ) / 2) hs.2 hq.2 ht
  have hκ : (bandScale M : ℝ) ≤ 1 / 64 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (bandScale_le M)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  simp only [compiledInput, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hlow hhigh
  constructor <;> linarith

theorem recorder_flow_halting_iff (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (upper : ℝ) (hupper : (7 / 8 : ℝ) ≤ upper)
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow (compiledInput I.1 hI.1).period
      (compiledInput I.1 hI.1).realizingVelocity Φ) :
    (∃ t : ℝ, 0 ≤ t ∧ 1 / 2 < Φ t
      (atHeight (codedPoint I.1 (finiteInitializedRecorder I hI)) (1 / 2)) 0 ∧
      Φ t (atHeight (codedPoint I.1 (finiteInitializedRecorder I hI)) (1 / 2)) 0 < upper) ↔
        Alternating.Halts I := by
  constructor
  · rintro ⟨t, ht, hx, _⟩
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
    let C₀ := finiteInitializedRecorder I hI
    have hs (n : ℕ) : Steps (finiteMachine I.1 hI.1) n C₀
        (run (finiteMachine I.1 hI.1) C₀ n) :=
      run_steps_of_nonhalting _ _ _ 2 (by norm_num) hn n
    have hnext (n : ℕ) : Step (finiteMachine I.1 hI.1)
        (run (finiteMachine I.1 hI.1) C₀ n) (run (finiteMachine I.1 hI.1) C₀ (n + 1)) :=
      run_step_of_nonhalting (finiteMachine I.1 hI.1) (initialState I.1)
        (initialAlphabet I hI) 2 (by norm_num) hn n
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
    have hsafe := (hnext n).flow_safe (hcontrol n) (hcontrol (n + 1)) hΦ
      (show t - (n : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> linarith)
    have he := (hs n).flow_nat hΦ
    have htime : t = (t - (n : ℝ)) + (n : ℝ) := by ring
    rw [htime, hΦ.nat_shift (realizingVelocity_time_periodic _) n, he] at hx
    linarith [hsafe.2]
  · intro hhalt
    obtain ⟨n, C, q, hs, hc, hh⟩ := (finite_recorder_halts_iff I hI).mpr hhalt
    have he := hs.flow_nat hΦ
    have hob := (codedPoint_observation_iff I.1 C).mpr
      (by simpa only [hc, recorderHalting] using hh)
    refine ⟨n, Nat.cast_nonneg _, ?_⟩
    rw [he]
    exact ⟨hob.1, hob.2.trans_le hupper⟩

end ForcedComputation.Recorder

end

end OAI
