import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FreshBranches
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderLoader
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.Subprogram
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SmallTranslation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.HeightShift

namespace OAI

/-! A small loading rectangle at the unused initial checkpoint. The incoming
checkpoint row is removed; all remaining target rectangles stay separated
from the loader, and all sources stay below its fixed source. -/

noncomputable section
namespace ForcedComputation.Recorder
open ShearFlows Radix Set

theorem stateBox_second_bounds (M : Alternating.Machine)
    (q : Control (State M) (Alphabet M)) {R : RationalBox 2} (hR : InUnit R)
    {x : Plane} (hx : x ∈ (scaledBox (bandScale M) (stateOffset M q) R).carrier) :
    (centerY M q : ℝ) - (bandScale M : ℝ) / 2 ≤ x 1 ∧
      x 1 ≤ (centerY M q : ℝ) + (bandScale M : ℝ) / 2 := by
  have h := scaledBox_between (bandScale_pos M).le (stateOffset M q) hR hx 1
  dsimp [stateOffset] at h
  push_cast at h
  constructor <;> linarith [h.1, h.2]

theorem codedPoint_second_bounds (M : Alternating.Machine)
    (C : Configuration (State M) (Alphabet M)) :
    (centerY M C.control : ℝ) - (bandScale M : ℝ) / 2 ≤ codedPoint M C 1 ∧
      codedPoint M C 1 ≤ (centerY M C.control : ℝ) + (bandScale M : ℝ) / 2 := by
  have hB : (1 : ℝ) < radixBase M := by exact_mod_cast radixBase_gt_one M
  have hd : ∀ a, (0 : ℝ) ≤ radixDigit M a ∧
      (radixDigit M a : ℝ) ≤ (radixBase M : ℝ) - 1 := by
    intro a
    exact ⟨(radixDigit_bounds M a).1, by linarith [(radixDigit_bounds M a).2]⟩
  have he := encode_mem_unit hB hd (tapeAt C).2
  have hk : (0 : ℝ) < bandScale M := by exact_mod_cast bandScale_pos M
  change _ ≤ (stateOffset M C.control 1 : ℝ) + (bandScale M : ℝ) *
    encode (radixBase M) (fun a => (radixDigit M a : ℝ)) (tapeAt C).2 ∧
    (stateOffset M C.control 1 : ℝ) + (bandScale M : ℝ) *
    encode (radixBase M) (fun a => (radixDigit M a : ℝ)) (tapeAt C).2 ≤ _
  simp only [stateOffset, Matrix.cons_val_one, Matrix.cons_val_zero, Rat.cast_sub,
    Rat.cast_div, Rat.cast_ofNat]
  constructor <;> nlinarith [he.1, he.2]

theorem bandScale_le_real (M : Alternating.Machine) : (bandScale M : ℝ) ≤ 1 / 64 := by
  have h := (Rat.cast_le (K := ℝ)).mpr (bandScale_le M)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

theorem centerY_bounds_real (M : Alternating.Machine) (q : Control (State M) (Alphabet M)) :
    (3 / 8 : ℝ) < centerY M q ∧ (centerY M q : ℝ) < 7 / 16 := by
  have hl := (Rat.cast_lt (K := ℝ)).mpr (centerY_bounds M q).1
  have hu := (Rat.cast_lt (K := ℝ)).mpr (centerY_bounds M q).2
  constructor
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using hl
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using hu

theorem codedPoint_in_compiledCenters (M : Alternating.Machine) (hM : M.WellFormed)
    (C : Configuration (State M) (Alphabet M)) :
    codedPoint M C ∈ (compiledInput M hM).centers.carrier := by
  have hB : (1 : ℝ) < radixBase M := by exact_mod_cast radixBase_gt_one M
  have hd : ∀ a, (0 : ℝ) ≤ radixDigit M a ∧
      (radixDigit M a : ℝ) ≤ (radixBase M : ℝ) - 1 := by
    intro a
    exact ⟨(radixDigit_bounds M a).1, by linarith [(radixDigit_bounds M a).2]⟩
  have hx := encode_mem_unit hB hd (tapeAt C).1
  have hy := codedPoint_second_bounds M C
  have hk : (0 : ℝ) < bandScale M := by exact_mod_cast bandScale_pos M
  have hk' := bandScale_le_real M
  have hc : (3 / 8 : ℝ) < centerY M C.control ∧
      (centerY M C.control : ℝ) < 7 / 16 := by
    exact centerY_bounds_real M C.control
  intro j
  fin_cases j
  · norm_num [compiledInput]
    rw [codedPoint_first]
    cases hh : recorderHalting M C.control <;>
      simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals constructor <;> nlinarith [hx.1, hx.2]
  · norm_num [compiledInput]
    constructor <;> linarith [hy.1, hy.2, hc.1, hc.2]

def periodicLoaderStart : Fin 2 → ℚ := ![1 / 4, 1 / 2]

def periodicLoaderRadius (M : Alternating.Machine) : ℚ := bandScale M / 8

def periodicLoaderInstruction (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Instruction :=
  ⟨centeredBox periodicLoaderStart (periodicLoaderRadius I.1),
    centeredBox (initialPointQ I hI) (periodicLoaderRadius I.1), 1⟩

theorem periodicLoaderInstruction_image (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    (periodicLoaderInstruction I hI).affine ''
      (periodicLoaderInstruction I hI).source.carrier =
      (periodicLoaderInstruction I hI).target.carrier := by
  apply Instruction.image_eq_of_halfWidths _ (by norm_num [periodicLoaderInstruction])
  · simp only [periodicLoaderInstruction, centeredBox_halfWidth, Rat.cast_one, one_mul]
  · simp only [periodicLoaderInstruction, centeredBox_halfWidth, Rat.cast_one, div_one]

theorem periodicLoader_source_separated (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (b : Branch (finiteMachine I.1 hI.1)) :
    PositivelySeparated (periodicLoaderInstruction I hI).source.carrier
      (geometricInstruction I.1 hI.1 b).source.carrier := by
  apply CoordinateGap.positiveSeparated (by norm_num : (0 : ℝ) < 1 / 32)
  intro x hx y hy
  have hx1 := hx 1
  change ((periodicLoaderStart 1 - periodicLoaderRadius I.1 : ℚ) : ℝ) ≤ x 1 ∧
    x 1 ≤ ((periodicLoaderStart 1 + periodicLoaderRadius I.1 : ℚ) : ℝ) at hx1
  norm_num only [periodicLoaderStart, Matrix.cons_val_one, Matrix.cons_val_zero,
    periodicLoaderRadius, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at hx1
  have hy1 := stateBox_second_bounds I.1 b.source
    (geometricInstruction_source_unit I.1 hI.1 b) hy
  have hc : (centerY I.1 b.source : ℝ) < 7 / 16 := by
    exact (centerY_bounds_real I.1 b.source).2
  have hk := bandScale_le_real I.1
  refine ⟨1, ?_⟩
  exact (show (1 / 32 : ℝ) ≤ x 1 - y 1 by linarith [hx1.1, hy1.2]).trans
    (le_abs_self _)

theorem periodicLoader_target_separated (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (b : Branch (finiteMachine I.1 hI.1))
    (hb : b.target ≠ (finiteInitializedRecorder I hI).control) :
    PositivelySeparated (periodicLoaderInstruction I hI).target.carrier
      (geometricInstruction I.1 hI.1 b).target.carrier := by
  have hk : (0 : ℝ) < bandScale I.1 := by exact_mod_cast bandScale_pos I.1
  apply CoordinateGap.positiveSeparated (mul_pos (by norm_num : (0 : ℝ) < 2) hk)
  intro x hx y hy
  have hx1 := hx 1
  change ((initialPointQ I hI 1 - periodicLoaderRadius I.1 : ℚ) : ℝ) ≤ x 1 ∧
    x 1 ≤ ((initialPointQ I hI 1 + periodicLoaderRadius I.1 : ℚ) : ℝ) at hx1
  simp only [periodicLoaderRadius, Rat.cast_sub, Rat.cast_add, Rat.cast_div,
    Rat.cast_ofNat] at hx1
  have hi := codedPoint_second_bounds I.1 (finiteInitializedRecorder I hI)
  rw [← initialPointQ_spec I hI] at hi
  have hy1 := stateBox_second_bounds I.1 b.target
    (geometricInstruction_target_unit I.1 hI.1 b) hy
  have hgap := centerY_gap I.1 hb
  refine ⟨1, ?_⟩
  rcases le_total (centerY I.1 b.target : ℝ)
      (centerY I.1 (finiteInitializedRecorder I hI).control : ℝ) with he | he
  · rw [abs_of_nonpos (sub_nonpos.mpr he)] at hgap
    exact (show 2 * (bandScale I.1 : ℝ) ≤ x 1 - y 1 by
      linarith [hx1.1, hy1.2, hi.1]).trans (le_abs_self _)
  · rw [abs_of_nonneg (sub_nonneg.mpr he)] at hgap
    calc
      2 * (bandScale I.1 : ℝ) ≤ y 1 - x 1 := by linarith [hx1.2, hy1.1, hi.2]
      _ ≤ |y 1 - x 1| := le_abs_self _
      _ = |x 1 - y 1| := abs_sub_comm _ _

def filteredGeometricBranches (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :=
  (geometricBranches I.1 (Alternating.ValidInput.machine_wellFormed hI)).filter
    fun b => decide (b.target ≠ (finiteInitializedRecorder I hI).control)

def loadedInput (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Input :=
  (compiledInput I.1 (Alternating.ValidInput.machine_wellFormed hI)).withInstructions
    (periodicLoaderInstruction I hI ::
      (filteredGeometricBranches I hI).map (geometricInstruction I.1 (Alternating.ValidInput.machine_wellFormed hI)))

def freshGeometricBranches (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :=
  filteredGeometricBranches (freshInput I) (freshInput_valid hI)

def periodicLoadedInput (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Input :=
  loadedInput (freshInput I) (freshInput_valid hI)

theorem periodicLoader_single_valid (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    ValidInput ((compiledInput I.1 hI.1).withInstructions [periodicLoaderInstruction I hI]) := by
  apply translationInstruction_singleton_valid (compiledInput_valid I.1 hI.1)
    periodicLoaderStart (initialPointQ I hI)
  · exact div_pos (bandScale_pos I.1) (by norm_num)
  · change bandScale I.1 / 8 ≤ bandScale I.1 / 2
    linarith [bandScale_pos I.1]
  · intro j
    fin_cases j <;> norm_num [compiledInput, periodicLoaderStart]
  · rw [initialPointQ_spec I hI]
    exact codedPoint_in_compiledCenters I.1 hI.1 _

theorem loadedInput_valid (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : ValidInput (loadedInput I hI) := by
  let bs := filteredGeometricBranches I hI
  let F := geometricInstruction I.1 hI.1
  have hsub : (bs.map F).Sublist (compiledInput I.1 hI.1).instructions :=
    List.Sublist.map F List.filter_sublist
  change ValidInput ((compiledInput I.1 hI.1).withInstructions
    (periodicLoaderInstruction I hI :: bs.map F))
  apply (compiledInput_valid I.1 hI.1).prependSublist hsub
    (periodicLoaderInstruction I hI) (periodicLoader_single_valid I hI)
  · intro c hc
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
    exact periodicLoader_source_separated I hI b
  · intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    have hne := (List.mem_filter.mp hb).2
    exact periodicLoader_target_separated I hI b (of_decide_eq_true hne)

theorem periodicLoadedInput_valid (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : ValidInput (periodicLoadedInput I hI) :=
  loadedInput_valid (freshInput I) (freshInput_valid hI)

theorem periodicLoadedInput_geometric_mem (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    (hb : b.target ≠ (finiteInitializedRecorder (freshInput I) (freshInput_valid hI)).control) :
    geometricInstruction (freshMachine I.1) (freshInput_valid hI).1 b ∈
      (periodicLoadedInput I hI).instructions := by
  classical
  apply List.mem_cons_of_mem
  apply List.mem_map.mpr
  refine ⟨b, List.mem_filter.mpr ⟨?_, decide_eq_true hb⟩, rfl⟩
  change b ∈ (compileBranches (freshMachine I.1) (freshInput_valid hI).1).dedup
  exact List.mem_dedup.mpr (mem_compileBranches (freshMachine I.1) (freshInput_valid hI).1 b)

theorem periodicLoadedInput_used_mem (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {n : ℕ}
    {C : Configuration (State (freshMachine I.1)) (Alphabet (freshMachine I.1))}
    (hc : Steps (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) n
      (finiteInitializedRecorder (freshInput I) (freshInput_valid hI)) C)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    (hs : b.source = C.control) :
    geometricInstruction (freshMachine I.1) (freshInput_valid hI).1 b ∈
      (periodicLoadedInput I hI).instructions := by
  have hzero : FreshControl (initialState (freshMachine I.1))
      (finiteInitializedRecorder (freshInput I) (freshInput_valid hI)).control := by
    constructor <;> intro he <;> cases he
  have hC := hc.freshControl (fresh_finiteMachine_next I.1 (freshInput_valid hI).1) hzero
  apply periodicLoadedInput_geometric_mem I hI b
  change b.target ≠ Control.checkpoint (initialState (freshMachine I.1))
  exact b.rule.not_fresh_checkpoint (by simpa only [hs] using hC)

def periodicInitializedInput (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Input :=
  (periodicLoadedInput I hI).shiftHeight (-(1 / 4))

theorem periodicInitializedInput_valid (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : ValidInput (periodicInitializedInput I hI) :=
  (periodicLoadedInput_valid I hI).shiftHeight _

@[simp] theorem periodicInitializedInput_height (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : (periodicInitializedInput I hI).codingHeight = 1 / 4 := by
  norm_num [periodicInitializedInput, Input.shiftHeight, periodicLoadedInput, loadedInput, Input.withInstructions, compiledInput]

@[simp] theorem periodicInitializedInput_period (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : (periodicInitializedInput I hI).period = 1 := rfl

end ForcedComputation.Recorder

end

end OAI
