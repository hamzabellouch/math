import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarRecorder
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicLoaderGeometry
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.UnitSpatialClock

namespace OAI

/-! The rational normalization of the planar initial condition. The fresh
machine starts in a nonhalting band, so the normalization preserves the fixed
halting strip and the unit-speed spatial clock on all coding rectangles. -/

noncomputable section

namespace ForcedComputation.Recorder.Planar

open ShearFlows Radix Set

theorem compression_le_real (M : Alternating.Machine) (hM : M.WellFormed) :
    (compression M hM : ℝ) ≤ 1 / 64 := by
  have h := (Rat.cast_le (K := ℝ)).mpr (compression_le M hM)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

theorem point_horizontal_bound (M : Alternating.Machine) (hM : M.WellFormed)
    (C : Configuration (State M) (Alphabet M)) :
    |point M hM C 0 - 1 / 4| ≤ (compression M hM : ℝ) / 8 := by
  have hy := codedPoint_second_bounds M C
  have hc := centerY_bounds_real M C.control
  have hk := bandScale_le_real M
  have hlo : (1 / 4 : ℝ) ≤ codedPoint M C 1 := by linarith [hy.1, hc.1]
  have hhi : codedPoint M C 1 ≤ (1 / 2 : ℝ) := by linarith [hy.2, hc.2]
  have hε : (0 : ℝ) < compression M hM := by exact_mod_cast compression_pos M hM
  change |(shift M hM : ℝ) + (compression M hM : ℝ) * codedPoint M C 1 - 1 / 4| ≤ _
  simp only [shift, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one]
  apply abs_le.mpr
  constructor <;> nlinarith

theorem point_vertical_bound (M : Alternating.Machine) (hM : M.WellFormed)
    (C : Configuration (State M) (Alphabet M)) :
    |point M hM C 1 - (if recorderHalting M C.control then (5 / 64 : ℝ) else 1 / 4)| ≤
      3 * (bandScale M : ℝ) / 16 := by
  have hB : (1 : ℝ) < radixBase M := by exact_mod_cast radixBase_gt_one M
  have hd : ∀ a, (0 : ℝ) ≤ radixDigit M a ∧
      (radixDigit M a : ℝ) ≤ (radixBase M : ℝ) - 1 := by
    intro a
    exact ⟨(radixDigit_bounds M a).1, by linarith [(radixDigit_bounds M a).2]⟩
  have he := encode_mem_unit hB hd (tapeAt C).1
  have hk : (0 : ℝ) < bandScale M := by exact_mod_cast bandScale_pos M
  rw [point_second]
  apply abs_le.mpr
  constructor <;> nlinarith [he.1, he.2]

def initialShift (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) : Fin 2 → ℚ :=
  fun j => 1 / 4 - initialPoint I hI j

def shiftPoint (δ : Fin 2 → ℚ) (x : Plane) : Plane := fun j => x j + (δ j : ℝ)

theorem initialShift_spec (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    shiftPoint (initialShift I hI) (point I.1 hI.1 (finiteInitializedRecorder I hI)) =
      ![1 / 4, 1 / 4] := by
  rw [← initialPoint_spec I hI]
  funext j
  fin_cases j <;> simp [shiftPoint, initialShift]

theorem initialShift_small (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (hn : recorderHalting I.1 (finiteInitializedRecorder I hI).control = false) :
    |(initialShift I hI 0 : ℝ)| ≤ 1 / 512 ∧
      |(initialShift I hI 1 : ℝ)| ≤ 3 / 1024 := by
  have hx := point_horizontal_bound I.1 hI.1 (finiteInitializedRecorder I hI)
  have hy := point_vertical_bound I.1 hI.1 (finiteInitializedRecorder I hI)
  rw [hn] at hy
  simp only [Bool.false_eq_true, ite_false] at hy
  rw [← initialPoint_spec I hI] at hx hy
  have hε := compression_le_real I.1 hI.1
  have hk := bandScale_le_real I.1
  have h₀ : |(initialShift I hI 0 : ℝ)| = |(initialPoint I hI 0 : ℝ) - 1 / 4| := by
    simp only [initialShift, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    exact abs_sub_comm _ _
  have h₁ : |(initialShift I hI 1 : ℝ)| = |(initialPoint I hI 1 : ℝ) - 1 / 4| := by
    simp only [initialShift, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    exact abs_sub_comm _ _
  rw [h₀, h₁]
  constructor <;> linarith

theorem fresh_initial_nonhalting (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    recorderHalting (freshMachine I.1)
      (finiteInitializedRecorder (freshInput I) (freshInput_valid hI)).control = false := by
  change (freshMachine I.1).isHalting 0 = false
  exact freshMachine_not_halting_zero I.1

theorem initialShift_small_rat (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (hn : recorderHalting I.1 (finiteInitializedRecorder I hI).control = false) :
    |initialShift I hI 0| ≤ 1 / 512 ∧ |initialShift I hI 1| ≤ 3 / 1024 := by
  have hb := initialShift_small I hI hn
  constructor
  · apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hb.1
  · apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat] using hb.2

theorem shifted_nonhalting_height (M : Alternating.Machine) (hM : M.WellFormed)
    (C : Configuration (State M) (Alphabet M)) (δ : Fin 2 → ℚ)
    (hn : recorderHalting M C.control = false) (hδ : |(δ 1 : ℝ)| ≤ 3 / 1024) :
    3 / 16 ≤ shiftPoint δ (point M hM C) 1 ∧
      shiftPoint δ (point M hM C) 1 ≤ 7 / 8 := by
  have hy := point_vertical_bound M hM C
  rw [hn] at hy
  simp only [Bool.false_eq_true, ite_false] at hy
  have hk := bandScale_le_real M
  obtain ⟨hylo, hyhi⟩ := abs_le.mp hy
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hδ
  change 3 / 16 ≤ point M hM C 1 + (δ 1 : ℝ) ∧
    point M hM C 1 + (δ 1 : ℝ) ≤ 7 / 8
  constructor <;> linarith

/-- Halting points have the paper's fixed clearance from both edges of the
observer, including the rational initial normalization. -/
theorem shifted_halting_clearance (M : Alternating.Machine) (hM : M.WellFormed)
    (C : Configuration (State M) (Alphabet M)) (δ : Fin 2 → ℚ)
    (hh : recorderHalting M C.control = true) (hδ : |(δ 1 : ℝ)| ≤ 3 / 1024) :
    1 / 16 ≤ shiftPoint δ (point M hM C) 1 ∧
      shiftPoint δ (point M hM C) 1 ≤ 3 / 32 := by
  have hy := point_vertical_bound M hM C
  rw [hh] at hy
  simp only [ite_true] at hy
  have hk := bandScale_le_real M
  obtain ⟨hylo, hyhi⟩ := abs_le.mp hy
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hδ
  change 1 / 16 ≤ point M hM C 1 + (δ 1 : ℝ) ∧
    point M hM C 1 + (δ 1 : ℝ) ≤ 3 / 32
  constructor <;> linarith

theorem shifted_point_observer_iff (M : Alternating.Machine) (hM : M.WellFormed)
    (C : Configuration (State M) (Alphabet M)) (δ : Fin 2 → ℚ)
    (hδ : |(δ 1 : ℝ)| ≤ 3 / 1024) :
    shiftPoint δ (point M hM C) ∈ observer ↔ recorderHalting M C.control = true := by
  have hy := point_vertical_bound M hM C
  have hk := bandScale_le_real M
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hδ
  obtain ⟨hylo, hyhi⟩ := abs_le.mp hy
  change (1 / 32 < point M hM C 1 + (δ 1 : ℝ) ∧
    point M hM C 1 + (δ 1 : ℝ) < 1 / 8) ↔ _
  cases hh : recorderHalting M C.control <;>
    simp only [hh, Bool.false_eq_true, ite_false, ite_true] at hylo hyhi ⊢
  · constructor
    · intro h
      linarith [h.2]
    · exact False.elim
  · constructor
    · intro _
      trivial
    · intro _
      constructor <;> linarith

theorem shifted_coding_rectangle_clock (M : Alternating.Machine) (hM : M.WellFormed)
    (δ : Fin 2 → ℚ) (hδ₀ : |(δ 0 : ℝ)| ≤ 1 / 512)
    (hδ₁ : |(δ 1 : ℝ)| ≤ 3 / 1024) {x : Plane}
    (hx : |x 0 - 1 / 4| ≤ (compression M hM : ℝ) / 8 ∧
      (5 / 128 : ℝ) ≤ x 1 ∧ x 1 ≤ 19 / 64) :
    shiftPoint δ x ∈ clockRectangle.carrier := by
  obtain ⟨hd₀lo, hd₀hi⟩ := abs_le.mp hδ₀
  obtain ⟨hd₁lo, hd₁hi⟩ := abs_le.mp hδ₁
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx.1
  have hε := compression_le_real M hM
  intro j
  fin_cases j
  · change ((1 / 8 : ℚ) : ℝ) ≤ x 0 + (δ 0 : ℝ) ∧
      x 0 + (δ 0 : ℝ) ≤ ((7 / 8 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    constructor <;> linarith
  · change ((1 / 32 : ℚ) : ℝ) ≤ x 1 + (δ 1 : ℝ) ∧
      x 1 + (δ 1 : ℝ) ≤ ((7 / 8 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    constructor <;> linarith [hx.2.1, hx.2.2]

theorem shifted_instruction_source_clock (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (δ : Fin 2 → ℚ)
    (hδ₀ : |(δ 0 : ℝ)| ≤ 1 / 512) (hδ₁ : |(δ 1 : ℝ)| ≤ 3 / 1024)
    {x : Plane} (hx : x ∈ (instruction M hM b).source.carrier) :
    unitSpatialClock (shiftPoint δ x) = 1 :=
  unitSpatialClock_one (shifted_coding_rectangle_clock M hM δ hδ₀ hδ₁
    (instruction_source_bounds M hM b hx))

theorem shifted_instruction_target_clock (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (δ : Fin 2 → ℚ)
    (hδ₀ : |(δ 0 : ℝ)| ≤ 1 / 512) (hδ₁ : |(δ 1 : ℝ)| ≤ 3 / 1024)
    {x : Plane} (hx : x ∈ (instruction M hM b).target.carrier) :
    unitSpatialClock (shiftPoint δ x) = 1 :=
  unitSpatialClock_one (shifted_coding_rectangle_clock M hM δ hδ₀ hδ₁
    (instruction_target_bounds M hM b hx))

theorem shifted_run_observer_iff (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (δ : Fin 2 → ℚ)
    (hδ : |(δ 1 : ℝ)| ≤ 3 / 1024) :
    (∃ n, shiftPoint δ (point I.1 hI.1
      (run (finiteMachine I.1 hI.1) (finiteInitializedRecorder I hI) n)) ∈ observer) ↔
        Alternating.Halts I := by
  have he (C : Configuration (State I.1) (Alphabet I.1)) :
      shiftPoint δ (point I.1 hI.1 C) ∈ observer ↔ point I.1 hI.1 C ∈ observer :=
    (shifted_point_observer_iff I.1 hI.1 C δ hδ).trans (point_observer_iff I.1 hI.1 C).symm
  simp_rw [he]
  exact run_observer_iff I hI

theorem normalized_run_observer_iff (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    (∃ n, shiftPoint (initialShift (freshInput I) (freshInput_valid hI))
      (point (freshMachine I.1) (freshInput_valid hI).1
        (run (finiteMachine (freshMachine I.1) (freshInput_valid hI).1)
          (finiteInitializedRecorder (freshInput I) (freshInput_valid hI)) n)) ∈ observer) ↔
        Alternating.Halts I := by
  have hb := initialShift_small (freshInput I) (freshInput_valid hI)
    (fresh_initial_nonhalting I hI)
  exact (shifted_run_observer_iff (freshInput I) (freshInput_valid hI) _ hb.2).trans
    (freshInput_halts_iff hI)

end ForcedComputation.Recorder.Planar

end

end OAI
