import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.HeightShift
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderLoader

namespace OAI

/-! The same finite recorder operates on any rational horizontal sheet.
Only the chart height changes; all planar instructions are retained. -/

namespace ForcedComputation.Recorder
open ShearFlows Radix Set

def recorderInputAtHeight (M : Alternating.Machine) (hM : M.WellFormed) (z : ℚ) : Input :=
  (compiledInput M hM).shiftHeight (z - 1 / 2)

theorem recorderInputAtHeight_valid (M : Alternating.Machine)
    (hM : M.WellFormed) (z : ℚ) : ValidInput (recorderInputAtHeight M hM z) :=
  (compiledInput_valid M hM).shiftHeight _

@[simp] theorem recorderInputAtHeight_height (M : Alternating.Machine)
    (hM : M.WellFormed) (z : ℚ) : ((recorderInputAtHeight M hM z).codingHeight : ℝ) = z := by
  simp only [recorderInputAtHeight, Input.shiftHeight_codingHeight, compiledInput,
    Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  ring

@[simp] theorem recorderInputAtHeight_period (M : Alternating.Machine)
    (hM : M.WellFormed) (z : ℚ) : ((recorderInputAtHeight M hM z).period : ℝ) = 1 := by
  norm_num [recorderInputAtHeight, compiledInput, Input.shiftHeight]

@[simp] theorem recorderInputAtHeight_halfWidth (M : Alternating.Machine)
    (hM : M.WellFormed) (z : ℚ) :
    ((recorderInputAtHeight M hM z).h : ℝ) = (bandScale M : ℝ) / 2 := by
  simp only [recorderInputAtHeight, Input.shiftHeight, compiledInput,
    Rat.cast_div, Rat.cast_ofNat]

theorem Step.flow_oneAtHeight (z : ℚ) {M : Alternating.Machine} {hM : M.WellFormed}
    {C D : Configuration (State M) (Alphabet M)}
    (h : Step (finiteMachine M hM) C D)
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow (recorderInputAtHeight M hM z).period
      (recorderInputAtHeight M hM z).realizingVelocity Φ) :
    Φ 1 (atHeight (codedPoint M C) (z : ℝ)) = atHeight (codedPoint M D) (z : ℝ) := by
  obtain ⟨q, a, d, hl, rfl⟩ := h
  let b : Branch (finiteMachine M hM) :=
    ⟨C.control, C.tape C.head, q, a, d, C.tape (C.head - 1), hl⟩
  have hd := recorderInputAtHeight_valid M hM z
  have hmem : geometricInstruction M hM b ∈ (recorderInputAtHeight M hM z).instructions :=
    geometricInstruction_mem M hM b
  have hB := radixBase_gt_one M
  have hdigits : ∀ a, 0 ≤ radixDigit M a ∧ radixDigit M a ≤ radixBase M - 1 := by
    intro a
    exact ⟨(radixDigit_bounds_rat M a).1, by linarith [(radixDigit_bounds_rat M a).2]⟩
  have hc : codedPoint M C ∈ (geometricInstruction M hM b).source.carrier :=
    branchInstruction_contains hB hdigits (bandScale_pos M).le (stateOffset M) b C rfl rfl rfl
  have htube := sourceTube_contains (geometricInstruction M hM b)
    (recorderInputAtHeight M hM z).codingHeight (δ := ((recorderInputAtHeight M hM z).tubeRadius : ℝ))
    (by exact_mod_cast tubeRadius_pos hd)
    (Set.mem_image_of_mem (fun X => atHeight X (recorderInputAtHeight M hM z).codingHeight) hc)
  have he := realizingVelocity_periodMap hd hΦ hmem htube
  have ha := branchInstruction_step hB hdigits (bandScale M) (stateOffset M) b C rfl rfl rfl
  simp only [atHeight_horizontal] at he
  change Φ 1 (atHeight (codedPoint M C) (recorderInputAtHeight M hM z).codingHeight) =
    atHeight ((geometricInstruction M hM b).affine (codedPoint M C))
      (recorderInputAtHeight M hM z).codingHeight at he
  have ha' : (geometricInstruction M hM b).affine (codedPoint M C) =
      codedPoint M ⟨q, C.head + d, Function.update C.tape C.head a⟩ := ha
  rw [ha'] at he
  simpa only [recorderInputAtHeight_height] using he

theorem Steps.flow_natAtHeight (z : ℚ) {M : Alternating.Machine} {hM : M.WellFormed}
    {C D : Configuration (State M) (Alphabet M)} {n : ℕ}
    (h : Steps (finiteMachine M hM) n C D)
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow (recorderInputAtHeight M hM z).period
      (recorderInputAtHeight M hM z).realizingVelocity Φ) :
    Φ n (atHeight (codedPoint M C) (z : ℝ)) = atHeight (codedPoint M D) (z : ℝ) := by
  induction h with
  | zero C => simpa only [Nat.cast_zero] using hΦ.initial (atHeight (codedPoint M C) (z : ℝ))
  | @next n C D E h hs ih =>
    rw [Nat.cast_add, Nat.cast_one, add_comm,
      hΦ.nat_shift (realizingVelocity_time_periodic _) n 1, ih]
    exact hs.flow_oneAtHeight z hΦ

theorem Step.flow_safeAtHeight (z : ℚ) {M : Alternating.Machine} {hM : M.WellFormed}
    {C D : Configuration (State M) (Alphabet M)}
    (h : Step (finiteMachine M hM) C D)
    (hc : recorderHalting M C.control = false) (hd : recorderHalting M D.control = false)
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow (recorderInputAtHeight M hM z).period
      (recorderInputAtHeight M hM z).realizingVelocity Φ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < Φ t (atHeight (codedPoint M C) (z : ℝ)) 0 ∧
      Φ t (atHeight (codedPoint M C) (z : ℝ)) 0 < 1 / 2 := by
  obtain ⟨q, a, d, hl, rfl⟩ := h
  let b : Branch (finiteMachine M hM) :=
    ⟨C.control, C.tape C.head, q, a, d, C.tape (C.head - 1), hl⟩
  have hv := recorderInputAtHeight_valid M hM z
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
  simp only [recorderInputAtHeight_height, recorderInputAtHeight_halfWidth] at hlow hhigh
  constructor <;> linarith

theorem recorder_flow_halting_iff_atHeight (z : ℚ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (upper : ℝ) (hupper : (7 / 8 : ℝ) ≤ upper)
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow (recorderInputAtHeight I.1 hI.1 z).period
      (recorderInputAtHeight I.1 hI.1 z).realizingVelocity Φ) :
    (∃ t : ℝ, 0 ≤ t ∧ 1 / 2 < Φ t
      (atHeight (codedPoint I.1 (finiteInitializedRecorder I hI)) (z : ℝ)) 0 ∧
      Φ t (atHeight (codedPoint I.1 (finiteInitializedRecorder I hI)) (z : ℝ)) 0 < upper) ↔
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
    have hsafe := (hnext n).flow_safeAtHeight z (hcontrol n) (hcontrol (n + 1)) hΦ
      (show t - (n : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> linarith)
    have he := (hs n).flow_natAtHeight z hΦ
    have htime : t = (t - (n : ℝ)) + (n : ℝ) := by ring
    rw [htime, hΦ.nat_shift (realizingVelocity_time_periodic _) n, he] at hx
    linarith [hsafe.2]
  · intro hhalt
    obtain ⟨n, C, q, hs, hc, hh⟩ := (finite_recorder_halts_iff I hI).mpr hhalt
    have he := hs.flow_natAtHeight z hΦ
    have hob := (codedPoint_observation_iff I.1 C).mpr
      (by simpa only [hc, recorderHalting] using hh)
    refine ⟨n, Nat.cast_nonneg _, ?_⟩
    rw [he]
    exact ⟨hob.1, hob.2.trans_le hupper⟩

end ForcedComputation.Recorder

end OAI
