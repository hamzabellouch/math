import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderInputEncoding
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderObservation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InitializedObservation

namespace OAI

/-! The finite input determines the rational endpoint of the one-period loader. -/

namespace ForcedComputation.Recorder
open Radix ShearFlows

def initialCoordinatesQ (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : ℚ × ℚ :=
  (radixDigit I.1 (recorderBlank I.1) / (radixBase I.1 - 1),
    finiteCode (radixBase I.1) (radixDigit I.1) (initialRightWord I hI) (recorderBlank I.1))

def initialPointQ (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : Fin 2 → ℚ :=
  letI := ShearFlows.neZeroTwo
  fun j => stateOffset I.1 (finiteInitializedRecorder I hI).control j + bandScale I.1 *
    (if j = 0 then (initialCoordinatesQ I hI).1 else (initialCoordinatesQ I hI).2)

theorem initialPointQ_spec (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    (fun j => (initialPointQ I hI j : ℝ)) =
      codedPoint I.1 (finiteInitializedRecorder I hI) := by
  have hd : ∀ a, 0 ≤ radixDigit I.1 a ∧ radixDigit I.1 a ≤ radixBase I.1 - 1 := by
    intro a
    exact ⟨(radixDigit_bounds_rat I.1 a).1, by linarith [(radixDigit_bounds_rat I.1 a).2]⟩
  have he := initial_coordinates_rational I hI (radixBase_gt_one I.1) hd
  funext j
  fin_cases j <;>
    norm_num [initialPointQ, initialCoordinatesQ, codedPoint, configurationPoint,
      embedPlane, planeOfPair, he]

private theorem coordinates_unit (M : Alternating.Machine)
    (C : Configuration (State M) (Alphabet M)) :
    (coordinates (radixBase M) (fun a => (radixDigit M a : ℝ)) (tapeAt C)).1 ∈ Set.Icc 0 1 ∧
    (coordinates (radixBase M) (fun a => (radixDigit M a : ℝ)) (tapeAt C)).2 ∈ Set.Icc 0 1 := by
  have hB : (1 : ℝ) < radixBase M := by exact_mod_cast radixBase_gt_one M
  have hd : ∀ a, (0 : ℝ) ≤ radixDigit M a ∧
      (radixDigit M a : ℝ) ≤ (radixBase M : ℝ) - 1 := by
    intro a
    exact ⟨(radixDigit_bounds M a).1, by linarith [(radixDigit_bounds M a).2]⟩
  exact ⟨encode_mem_unit hB hd _, encode_mem_unit hB hd _⟩

theorem codedPoint_in_loader_chart (M : Alternating.Machine)
    (C : Configuration (State M) (Alphabet M)) (j : Fin 2) :
    1 / 8 ≤ codedPoint M C j ∧ codedPoint M C j ≤ 7 / 8 := by
  obtain ⟨hx, hy⟩ := coordinates_unit M C
  have hκ : (0 : ℝ) < bandScale M := by exact_mod_cast bandScale_pos M
  have hκ' : (bandScale M : ℝ) ≤ 1 / 64 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (bandScale_le M)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  have hcenter : (3 / 8 : ℝ) < centerY M C.control ∧
      (centerY M C.control : ℝ) < 7 / 16 := by
    have h := centerY_bounds M C.control
    exact ⟨by simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr h.1,
      by simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr h.2⟩
  fin_cases j
  · change (1 / 8 : ℝ) ≤ codedPoint M C 0 ∧ codedPoint M C 0 ≤ 7 / 8
    rw [codedPoint_first]
    change 0 ≤ encode (radixBase M) (fun a => (radixDigit M a : ℝ)) (tapeAt C).1 ∧
      encode (radixBase M) (fun a => (radixDigit M a : ℝ)) (tapeAt C).1 ≤ 1 at hx
    cases ht : recorderHalting M C.control <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals constructor <;> nlinarith [hx.1, hx.2]
  · change (1 / 8 : ℝ) ≤ (stateOffset M C.control 1 : ℝ) + (bandScale M : ℝ) *
        (coordinates (radixBase M) (fun a => (radixDigit M a : ℝ)) (tapeAt C)).2 ∧
      (stateOffset M C.control 1 : ℝ) + (bandScale M : ℝ) *
        (coordinates (radixBase M) (fun a => (radixDigit M a : ℝ)) (tapeAt C)).2 ≤ 7 / 8
    simp only [stateOffset, Matrix.cons_val_one, Matrix.cons_val_zero, Rat.cast_sub,
      Rat.cast_div, Rat.cast_ofNat]
    constructor <;> nlinarith [hy.1, hy.2, hcenter.1, hcenter.2]

theorem initialPointQ_bounds (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (j : Fin 2) : 1 / 8 ≤ initialPointQ I hI j ∧ initialPointQ I hI j ≤ 7 / 8 := by
  have h := codedPoint_in_loader_chart I.1 (finiteInitializedRecorder I hI) j
  rw [← initialPointQ_spec I hI] at h
  exact ⟨(Rat.cast_le (K := ℝ)).mp (by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h.1),
    (Rat.cast_le (K := ℝ)).mp (by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using h.2)⟩

def recorderLoader (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : Input :=
  loaderInput fixedStart (initialPointQ I hI) (1 / 2)

theorem recorderLoader_valid (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    ValidInput (recorderLoader I hI) :=
  loaderInput_valid _ _ _ (by intro j; fin_cases j <;> norm_num [fixedStart])
    (initialPointQ_bounds I hI) (by norm_num)

end ForcedComputation.Recorder

end OAI
