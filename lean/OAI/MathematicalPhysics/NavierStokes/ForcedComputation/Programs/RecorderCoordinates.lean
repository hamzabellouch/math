import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.Branches
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ConfigurationTapes
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InstructionRectangles

namespace OAI

/-! The actual recorder step agrees with its filled-rectangle affine instruction. -/

noncomputable section

namespace ForcedComputation.Recorder

open Radix ShearFlows

variable {Q A : Type*}

def headMoveOfInt (d : ℤ) : HeadMove :=
  if d = -1 then .left else if d = 0 then .stay else .right

theorem LocalStep.displacement_bounds {M : Machine Q A} {q q' : Control Q A}
    {s s' : Symbol Q A} {d : ℤ} (h : LocalStep M q s q' s' d) : -1 ≤ d ∧ d ≤ 1 := by
  cases h <;> first | exact M.move_bound _ _ | norm_num

theorem tape_coordinates_update {B : ℝ} {digit : Symbol Q A → ℝ}
    (hB : 1 < B) (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1)
    (C : Configuration Q A) (q' : Control Q A) (b : Symbol Q A)
    (d : ℤ) (hlo : -1 ≤ d) (hhi : d ≤ 1) :
    coordinates B digit (tapeAt ⟨q', C.head + d, Function.update C.tape C.head b⟩) =
      normalizedMove B (digit (C.tape (C.head - 1))) (digit (C.tape C.head)) (digit b)
        (headMoveOfInt d) (coordinates B digit (tapeAt C)) := by
  have hc : d = -1 ∨ d = 0 ∨ d = 1 := by omega
  rcases hc with rfl | rfl | rfl
  · have h := congrArg (coordinates B digit) (tapeAt_left C q' b)
    rw [coordinates_left hB hd] at h
    simpa only [headMoveOfInt, ite_eq_left, normalizedMove, tapeAt,
      Nat.cast_zero, zero_add, add_zero, sub_eq_add_neg] using h
  · have h := congrArg (coordinates B digit) (tapeAt_stay C q' b)
    rw [coordinates_stay hB hd] at h
    simpa only [headMoveOfInt, show (0 : ℤ) ≠ -1 by norm_num, ite_false, ite_eq_left,
      normalizedMove, tapeAt, Nat.cast_zero, add_zero] using h
  · have h := congrArg (coordinates B digit) (tapeAt_right C q' b)
    rw [coordinates_right hB hd] at h
    simpa only [headMoveOfInt, show (1 : ℤ) ≠ -1 by norm_num,
      show (1 : ℤ) ≠ 0 by norm_num, ite_false, normalizedMove, tapeAt,
      Nat.cast_zero, add_zero] using h

def configurationPoint (κ B : ℚ) (digit : Symbol Q A → ℚ)
    (offset : Control Q A → Fin 2 → ℚ) (C : Configuration Q A) : Plane :=
  embedPlane κ (offset C.control)
    (planeOfPair (coordinates B (fun a => (digit a : ℝ)) (tapeAt C)))

def branchInstruction {M : Machine Q A} (κ B : ℚ) (digit : Symbol Q A → ℚ)
    (offset : Control Q A → Fin 2 → ℚ) (b : Branch M) : Instruction :=
  scaledInstruction κ (offset b.source) (offset b.target)
    (radixInstruction B (digit b.left) (digit b.read) (digit b.write)
      (headMoveOfInt b.displacement))

theorem embedPlane_mem_scaledBox {κ : ℚ} (hκ : 0 ≤ κ)
    (offset : Fin 2 → ℚ) {R : RationalBox 2} {x : Plane} (hx : x ∈ R.carrier) :
    embedPlane κ offset x ∈ (scaledBox κ offset R).carrier := by
  have hκr : (0 : ℝ) ≤ κ := by exact_mod_cast hκ
  intro j
  change ((offset j + κ * R.lower j : ℚ) : ℝ) ≤
      (offset j : ℝ) + (κ : ℝ) * x j ∧
    (offset j : ℝ) + (κ : ℝ) * x j ≤ ((offset j + κ * R.upper j : ℚ) : ℝ)
  simp only [Rat.cast_add, Rat.cast_mul]
  exact ⟨add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hx j).1 hκr),
    add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hx j).2 hκr)⟩

theorem branchInstruction_contains {M : Machine Q A} {B : ℚ} (hB : 1 < B)
    {digit : Symbol Q A → ℚ} (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1)
    {κ : ℚ} (hκ : 0 ≤ κ) (offset : Control Q A → Fin 2 → ℚ) (b : Branch M)
    (C : Configuration Q A) (hs : C.control = b.source)
    (hr : C.tape C.head = b.read) (hl : C.tape (C.head - 1) = b.left) :
    configurationPoint κ B digit offset C ∈ (branchInstruction κ B digit offset b).source.carrier := by
  have hBr : (1 : ℝ) < B := by exact_mod_cast hB
  have hdr : ∀ a, (0 : ℝ) ≤ digit a ∧ (digit a : ℝ) ≤ (B : ℝ) - 1 := by
    intro a
    constructor
    · exact_mod_cast (hd a).1
    · exact_mod_cast (hd a).2
  have hx := encode_in_first_cylinder hBr hdr (tapeAt C).1
  have hy := encode_in_first_cylinder hBr hdr (tapeAt C).2
  simp only [tapeAt, Nat.cast_zero, zero_add, add_zero, hl, hr] at hx hy
  unfold configurationPoint branchInstruction
  rw [hs]
  apply embedPlane_mem_scaledBox hκ
  intro j
  fin_cases j
  · dsimp [radixInstruction, sourceBox, planeOfPair, coordinates]
    simpa only [Set.mem_Icc, tapeAt, Rat.cast_div, Rat.cast_add, Rat.cast_one] using hx
  · dsimp [radixInstruction, sourceBox, planeOfPair, coordinates]
    simpa only [Set.mem_Icc, tapeAt, Rat.cast_div, Rat.cast_add, Rat.cast_one] using hy

theorem branchInstruction_step {M : Machine Q A} {B : ℚ} (hB : 1 < B)
    {digit : Symbol Q A → ℚ} (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1)
    (κ : ℚ) (offset : Control Q A → Fin 2 → ℚ) (b : Branch M)
    (C : Configuration Q A) (hs : C.control = b.source)
    (hr : C.tape C.head = b.read) (hl : C.tape (C.head - 1) = b.left) :
    (branchInstruction κ B digit offset b).affine (configurationPoint κ B digit offset C) =
      configurationPoint κ B digit offset
        ⟨b.target, C.head + b.displacement, Function.update C.tape C.head b.write⟩ := by
  have hBr : (1 : ℝ) < B := by exact_mod_cast hB
  have hdr : ∀ a, (0 : ℝ) ≤ digit a ∧ (digit a : ℝ) ≤ (B : ℝ) - 1 := by
    intro a
    constructor
    · exact_mod_cast (hd a).1
    · exact_mod_cast (hd a).2
  have hc := tape_coordinates_update hBr hdr C b.target b.write b.displacement
    b.rule.displacement_bounds.1 b.rule.displacement_bounds.2
  simp only [hr, hl] at hc
  unfold branchInstruction configurationPoint
  rw [hs, scaledInstruction_action, radixInstruction_action (by linarith : (0 : ℚ) < B), hc]

end ForcedComputation.Recorder

end

end OAI
