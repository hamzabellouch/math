import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarConjugacy
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderObservation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderLoader

namespace OAI

/-! A finite rational planar recorder program with the stationary-suspension
paper's horizontal initial corridor and low vertical halting observer. -/

noncomputable section

namespace ForcedComputation.Recorder.Planar

open ShearFlows Radix

/-- Horizontal compression accounts for the number of parking columns. -/
def compression (M : Alternating.Machine) (hM : M.WellFormed) : ℚ :=
  1 / (64 * ((geometricBranches M hM).length + 1))

theorem compression_pos (M : Alternating.Machine) (hM : M.WellFormed) :
    0 < compression M hM := by unfold compression; positivity

theorem compression_le (M : Alternating.Machine) (hM : M.WellFormed) :
    compression M hM ≤ 1 / 64 := by
  unfold compression
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  have h : (0 : ℚ) ≤ (geometricBranches M hM).length := by positivity
  nlinarith

def shift (M : Alternating.Machine) (hM : M.WellFormed) : ℚ :=
  1 / 4 - 3 * compression M hM / 8

def coordinateMap (M : Alternating.Machine) (hM : M.WellFormed) : Plane → Plane :=
  PlanarConjugacy.map (shift M hM) (43 / 128) (compression M hM) (11 / 32)

def instruction (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : Instruction :=
  PlanarConjugacy.instruction (shift M hM) (43 / 128) (compression M hM) (11 / 32)
    (geometricInstruction M hM b)

def program (M : Alternating.Machine) (hM : M.WellFormed) : List Instruction :=
  (geometricBranches M hM).map (instruction M hM)

def point (M : Alternating.Machine) (hM : M.WellFormed)
    (C : Configuration (State M) (Alphabet M)) : Plane :=
  coordinateMap M hM (codedPoint M C)

def observer : Set Plane :=
  letI := ShearFlows.neZeroTwo
  letI := ShearFlows.thirtyTwoAtLeastTwo
  letI := ShearFlows.eightAtLeastTwo
  {x | 1 / 32 < x 1 ∧ x 1 < 1 / 8}

/-- The input-dependent loading endpoint is a finite rational expression. -/
def initialPoint (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : Fin 2 → ℚ :=
  letI := ShearFlows.neZeroTwo
  ![shift I.1 (Alternating.ValidInput.machine_wellFormed hI) + compression I.1 (Alternating.ValidInput.machine_wellFormed hI) * initialPointQ I hI 1,
    43 / 128 - (11 / 32) * initialPointQ I hI 0]

theorem initialPoint_spec (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    (fun j => (initialPoint I hI j : ℝ)) = point I.1 hI.1 (finiteInitializedRecorder I hI) := by
  rw [point, coordinateMap, ← initialPointQ_spec I hI]
  funext j
  fin_cases j <;> simp [initialPoint, PlanarConjugacy.map]

theorem instruction_mem (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : instruction M hM b ∈ program M hM := by
  apply List.mem_map.mpr
  exact ⟨b, by simpa only [geometricBranches, List.mem_dedup] using mem_compileBranches M hM b, rfl⟩

theorem instruction_source_positive (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : (instruction M hM b).source.positive :=
  PlanarConjugacy.box_positive (compression_pos M hM) (by norm_num)
    (geometricInstruction_source_positive M hM b)

theorem instruction_target_positive (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : (instruction M hM b).target.positive :=
  PlanarConjugacy.box_positive (compression_pos M hM) (by norm_num)
    (geometricInstruction_target_positive M hM b)

theorem instruction_factor_pos (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : 0 < (instruction M hM b).factor :=
  PlanarConjugacy.instruction_factor_pos (geometricInstruction_factor_pos M hM b)

theorem instruction_image (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    (instruction M hM b).affine '' (instruction M hM b).source.carrier =
      (instruction M hM b).target.carrier :=
  PlanarConjugacy.instruction_image_eq (compression_pos M hM) (by norm_num)
    (geometricInstruction_factor_pos M hM b).ne' (geometricInstruction_image M hM b)

theorem instruction_source_separation (M : Alternating.Machine) (hM : M.WellFormed)
    {b c : Branch (finiteMachine M hM)} (hne : b ≠ c) :
    PositivelySeparated (instruction M hM b).source.carrier (instruction M hM c).source.carrier := by
  change PositivelySeparated (PlanarConjugacy.box _ _ _ _ _).carrier
    (PlanarConjugacy.box _ _ _ _ _).carrier
  rw [← PlanarConjugacy.box_image (compression_pos M hM) (by norm_num),
    ← PlanarConjugacy.box_image (compression_pos M hM) (by norm_num)]
  exact PlanarConjugacy.separated_image (compression_pos M hM) (by norm_num)
    (geometricInstruction_source_separation M hM hne)

theorem instruction_target_separation (M : Alternating.Machine) (hM : M.WellFormed)
    {b c : Branch (finiteMachine M hM)} (hne : b ≠ c) :
    PositivelySeparated (instruction M hM b).target.carrier (instruction M hM c).target.carrier := by
  change PositivelySeparated (PlanarConjugacy.box _ _ _ _ _).carrier
    (PlanarConjugacy.box _ _ _ _ _).carrier
  rw [← PlanarConjugacy.box_image (compression_pos M hM) (by norm_num),
    ← PlanarConjugacy.box_image (compression_pos M hM) (by norm_num)]
  exact PlanarConjugacy.separated_image (compression_pos M hM) (by norm_num)
    (geometricInstruction_target_separation M hM hne)

theorem instruction_halfWidths (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    (instruction M hM b).source.halfWidth 0 ≤ (compression M hM : ℝ) * (bandScale M : ℝ) / 2 ∧
    (instruction M hM b).target.halfWidth 0 ≤ (compression M hM : ℝ) * (bandScale M : ℝ) / 2 ∧
    (instruction M hM b).source.halfWidth 1 ≤ (3 / 8 : ℝ) * (bandScale M : ℝ) / 2 ∧
    (instruction M hM b).target.halfWidth 1 ≤ (3 / 8 : ℝ) * (bandScale M : ℝ) / 2 := by
  have hε : (0 : ℝ) ≤ compression M hM := by exact_mod_cast (compression_pos M hM).le
  have hs := PlanarConjugacy.box_halfWidth (shift M hM) (43 / 128) (compression M hM) (11 / 32)
    (geometricInstruction M hM b).source
  have ht := PlanarConjugacy.box_halfWidth (shift M hM) (43 / 128) (compression M hM) (11 / 32)
    (geometricInstruction M hM b).target
  simp only [instruction, PlanarConjugacy.instruction, hs, ht, Matrix.cons_val_zero,
    Matrix.cons_val_one, Rat.cast_div, Rat.cast_ofNat]
  have hκ : (0 : ℝ) ≤ bandScale M := by exact_mod_cast (bandScale_pos M).le
  have hx := geometricInstruction_halfWidths M hM b 1
  have hy := geometricInstruction_halfWidths M hM b 0
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hx.1 hε]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2 hε]
  · nlinarith [hy.1]
  · nlinarith [hy.2]

theorem coordinateMap_bounds (M : Alternating.Machine) (hM : M.WellFormed) {x : Plane}
    (hx : (1 / 8 : ℝ) ≤ x 0 ∧ x 0 ≤ 13 / 16 ∧ 1 / 4 ≤ x 1 ∧ x 1 ≤ 1 / 2) :
    |coordinateMap M hM x 0 - 1 / 4| ≤ (compression M hM : ℝ) / 8 ∧
      (5 / 128 : ℝ) ≤ coordinateMap M hM x 1 ∧ coordinateMap M hM x 1 ≤ 19 / 64 := by
  have hε : (0 : ℝ) < compression M hM := by exact_mod_cast compression_pos M hM
  simp only [coordinateMap, PlanarConjugacy.map, shift, Matrix.cons_val_zero,
    Matrix.cons_val_one, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat]
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]

theorem instruction_source_bounds (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x : Plane} (hx : x ∈ (instruction M hM b).source.carrier) :
    |x 0 - 1 / 4| ≤ (compression M hM : ℝ) / 8 ∧
      (5 / 128 : ℝ) ≤ x 1 ∧ x 1 ≤ 19 / 64 := by
  change x ∈ (PlanarConjugacy.box _ _ _ _ _).carrier at hx
  rw [← PlanarConjugacy.box_image (compression_pos M hM) (by norm_num)] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact coordinateMap_bounds M hM (geometricInstruction_source_bounds M hM b hy)

theorem instruction_target_bounds (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x : Plane} (hx : x ∈ (instruction M hM b).target.carrier) :
    |x 0 - 1 / 4| ≤ (compression M hM : ℝ) / 8 ∧
      (5 / 128 : ℝ) ≤ x 1 ∧ x 1 ≤ 19 / 64 := by
  change x ∈ (PlanarConjugacy.box _ _ _ _ _).carrier at hx
  rw [← PlanarConjugacy.box_image (compression_pos M hM) (by norm_num)] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact coordinateMap_bounds M hM (geometricInstruction_target_bounds M hM b hy)

theorem step_realized {M : Alternating.Machine} {hM : M.WellFormed}
    {C D : Configuration (State M) (Alphabet M)} (h : Step (finiteMachine M hM) C D) :
    ∃ b ∈ program M hM, point M hM C ∈ b.source.carrier ∧
      b.affine (point M hM C) = point M hM D := by
  obtain ⟨q, a, d, hl, rfl⟩ := h
  let b : Branch (finiteMachine M hM) :=
    ⟨C.control, C.tape C.head, q, a, d, C.tape (C.head - 1), hl⟩
  have hdigits : ∀ a, 0 ≤ radixDigit M a ∧ radixDigit M a ≤ radixBase M - 1 := by
    intro a
    exact ⟨(radixDigit_bounds_rat M a).1, by linarith [(radixDigit_bounds_rat M a).2]⟩
  have hx : codedPoint M C ∈ (geometricInstruction M hM b).source.carrier :=
    branchInstruction_contains (radixBase_gt_one M) hdigits (bandScale_pos M).le
      (stateOffset M) b C rfl rfl rfl
  have ha : (geometricInstruction M hM b).affine (codedPoint M C) =
      codedPoint M ⟨q, C.head + d, Function.update C.tape C.head a⟩ :=
    branchInstruction_step (radixBase_gt_one M) hdigits (bandScale M) (stateOffset M) b C rfl rfl rfl
  refine ⟨instruction M hM b, instruction_mem M hM b, ?_, ?_⟩
  · exact PlanarConjugacy.mem_box_of_mem (compression_pos M hM).le (by norm_num) hx
  · change (PlanarConjugacy.instruction _ _ _ _ _).affine
      (PlanarConjugacy.map _ _ _ _ (codedPoint M C)) = _
    rw [PlanarConjugacy.instruction_conjugacy _ _ _ _ _
      (geometricInstruction_factor_pos M hM b).ne', ha]
    rfl

theorem point_second (M : Alternating.Machine) (hM : M.WellFormed)
    (C : Configuration (State M) (Alphabet M)) :
    point M hM C 1 = (if recorderHalting M C.control then (5 / 64 : ℝ) else 1 / 4) -
      (11 / 32) * (bandScale M : ℝ) *
        (encode (radixBase M) (fun a => (radixDigit M a : ℝ)) (tapeAt C).1 - 1 / 2) := by
  change ((43 / 128 : ℚ) : ℝ) - ((11 / 32 : ℚ) : ℝ) * codedPoint M C 0 = _
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [codedPoint_first]
  cases hh : recorderHalting M C.control <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals ring

theorem point_observer_iff (M : Alternating.Machine) (hM : M.WellFormed)
    (C : Configuration (State M) (Alphabet M)) :
    point M hM C ∈ observer ↔ recorderHalting M C.control = true := by
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
  change (1 / 32 < point M hM C 1 ∧ point M hM C 1 < 1 / 8) ↔ _
  rw [point_second]
  cases hh : recorderHalting M C.control <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · constructor
    · intro h
      nlinarith [h.2]
    · exact False.elim
  · constructor
    · intro _
      trivial
    · intro _
      constructor <;> nlinarith

theorem run_observer_iff (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    (∃ n, point I.1 hI.1 (run (finiteMachine I.1 hI.1) (finiteInitializedRecorder I hI) n)
      ∈ observer) ↔ Alternating.Halts I := by
  simp_rw [point_observer_iff]
  have hh (q : Control (State I.1) (Alphabet I.1)) :
      recorderHalting I.1 q = haltingControl (finiteMachine I.1 hI.1) q := by cases q <;> rfl
  simp_rw [hh]
  change (∃ n, haltingControl (finiteMachine I.1 hI.1)
    (run (finiteMachine I.1 hI.1)
      (checkpointAt (finiteMachine I.1 hI.1) (initialState I.1) (initialAlphabet I hI) 2 0) n).control = true) ↔ _
  rw [run_halting_iff _ _ _ _ (by norm_num)]
  have hs (n : ℕ) := congrArg WorkConfiguration.state (finite_workAt I hI n)
  simp only [forgetWork, originalConfiguration] at hs
  change (∃ n, I.1.isHalting
    (workAt (finiteMachine I.1 hI.1) (initialState I.1) (initialAlphabet I hI) n).state.val = true) ↔ _
  simp only [hs, Alternating.Halts]

end ForcedComputation.Recorder.Planar

end

end OAI
