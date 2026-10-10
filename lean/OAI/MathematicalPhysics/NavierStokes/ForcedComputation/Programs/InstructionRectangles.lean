import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RectangleAffine
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.GappedInstructions

namespace OAI

/-! Rational filled rectangles and reciprocal affine maps for all three head
moves. These are the exact rows of the radix table in Section 4 of paper 379-01. -/

noncomputable section

namespace ForcedComputation.Radix

open ShearFlows

inductive HeadMove
  | left | stay | right
  deriving DecidableEq

def sourceBox (B l a : ℚ) : RationalBox 2 :=
  ⟨![l / B, a / B], ![(l + 1) / B, (a + 1) / B]⟩

def targetBox (B l b : ℚ) : HeadMove → RationalBox 2
  | .right => ⟨![b / B + l / B ^ 2, 0], ![b / B + (l + 1) / B ^ 2, 1]⟩
  | .stay => ⟨![l / B, b / B], ![(l + 1) / B, (b + 1) / B]⟩
  | .left => ⟨![0, l / B + b / B ^ 2], ![1, l / B + (b + 1) / B ^ 2]⟩

def headFactor (B : ℚ) : HeadMove → ℚ
  | .right => B⁻¹
  | .stay => 1
  | .left => B

def radixInstruction (B l a b : ℚ) (m : HeadMove) : Instruction :=
  ⟨sourceBox B l a, targetBox B l b m, headFactor B m⟩

theorem headFactor_pos {B : ℚ} (hB : 0 < B) (m : HeadMove) :
    0 < headFactor B m := by
  cases m <;> simp [headFactor, hB, inv_pos.mpr hB]

theorem sourceBox_positive {B : ℚ} (hB : 0 < B) (l a : ℚ) :
    (sourceBox B l a).positive := by
  intro j
  fin_cases j <;> dsimp [sourceBox]
  all_goals apply (div_lt_div_iff_of_pos_right hB).mpr; linarith

theorem targetBox_positive {B : ℚ} (hB : 0 < B) (l b : ℚ) (m : HeadMove) :
    (targetBox B l b m).positive := by
  have hBB : 0 < B ^ 2 := pow_pos hB 2
  have hdiv (x : ℚ) : x / B < (x + 1) / B :=
    (div_lt_div_iff_of_pos_right hB).mpr (by linarith)
  have hdiv2 (x : ℚ) : x / B ^ 2 < (x + 1) / B ^ 2 :=
    (div_lt_div_iff_of_pos_right hBB).mpr (by linarith)
  intro j
  cases m <;> fin_cases j <;> dsimp [targetBox]
  · norm_num
  · linarith [hdiv2 b]
  · exact hdiv l
  · exact hdiv b
  · linarith [hdiv2 l]
  · norm_num

theorem radixInstruction_image {B : ℚ} (hB : 0 < B) (l a b : ℚ) (m : HeadMove) :
    (radixInstruction B l a b m).affine '' (sourceBox B l a).carrier =
      (targetBox B l b m).carrier := by
  have hn : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  apply Instruction.image_eq_of_halfWidths _ (headFactor_pos hB m)
  all_goals cases m <;>
    simp only [radixInstruction, sourceBox, targetBox, headFactor, RationalBox.halfWidth,
      Matrix.cons_val_zero, Matrix.cons_val_one, Rat.cast_add, Rat.cast_div,
      Rat.cast_zero, Rat.cast_one, Rat.cast_pow, Rat.cast_inv] <;> field_simp <;> ring

def normalizedMove (B l a b : ℝ) : HeadMove → (ℝ × ℝ) → ℝ × ℝ
  | .right => rightMove B a b
  | .stay => stayMove B a b
  | .left => leftMove B l a b

def planeOfPair (p : ℝ × ℝ) : Plane := ![p.1, p.2]

theorem radixInstruction_action {B : ℚ} (hB : 0 < B) (l a b : ℚ)
    (m : HeadMove) (p : ℝ × ℝ) :
    (radixInstruction B l a b m).affine (planeOfPair p) =
      planeOfPair (normalizedMove B l a b m p) := by
  have hn : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  funext j
  cases m <;> fin_cases j <;>
    simp only [radixInstruction, sourceBox, targetBox, headFactor, normalizedMove,
      rightMove, leftMove, stayMove, planeOfPair, push, pop, Instruction.affine,
      RationalBox.center, Matrix.cons_val_zero, Matrix.cons_val_one,
      Rat.cast_add, Rat.cast_div, Rat.cast_zero, Rat.cast_one, Rat.cast_pow, Rat.cast_inv] <;>
    dsimp <;> field_simp <;> ring

def scaledBox (κ : ℚ) (offset : Fin 2 → ℚ) (R : RationalBox 2) : RationalBox 2 :=
  ⟨fun j => offset j + κ * R.lower j, fun j => offset j + κ * R.upper j⟩

theorem scaledBox_center (κ : ℚ) (offset : Fin 2 → ℚ) (R : RationalBox 2) (j : Fin 2) :
    (scaledBox κ offset R).center j = (offset j : ℝ) + (κ : ℝ) * R.center j := by
  simp only [scaledBox, RationalBox.center, Rat.cast_add, Rat.cast_mul]
  ring

theorem scaledBox_halfWidth (κ : ℚ) (offset : Fin 2 → ℚ) (R : RationalBox 2) (j : Fin 2) :
    (scaledBox κ offset R).halfWidth j = (κ : ℝ) * R.halfWidth j := by
  simp only [scaledBox, RationalBox.halfWidth, Rat.cast_add, Rat.cast_mul]
  ring

theorem scaledBox_positive {κ : ℚ} (hκ : 0 < κ) (offset : Fin 2 → ℚ)
    {R : RationalBox 2} (hR : R.positive) : (scaledBox κ offset R).positive := by
  intro j
  dsimp [scaledBox]
  linarith [mul_lt_mul_of_pos_left (hR j) hκ]

def scaledInstruction (κ : ℚ) (sourceOffset targetOffset : Fin 2 → ℚ)
    (b : Instruction) : Instruction :=
  ⟨scaledBox κ sourceOffset b.source, scaledBox κ targetOffset b.target, b.factor⟩

theorem scaledInstruction_image {κ : ℚ} (sourceOffset targetOffset : Fin 2 → ℚ)
    (b : Instruction) (hf : 0 < b.factor)
    (h₀ : b.target.halfWidth 0 = (b.factor : ℝ) * b.source.halfWidth 0)
    (h₁ : b.target.halfWidth 1 = b.source.halfWidth 1 / (b.factor : ℝ)) :
    (scaledInstruction κ sourceOffset targetOffset b).affine ''
        (scaledBox κ sourceOffset b.source).carrier =
      (scaledBox κ targetOffset b.target).carrier := by
  apply Instruction.image_eq_of_halfWidths (scaledInstruction κ sourceOffset targetOffset b) hf
  · change (scaledBox κ targetOffset b.target).halfWidth 0 =
      (b.factor : ℝ) * (scaledBox κ sourceOffset b.source).halfWidth 0
    rw [scaledBox_halfWidth, scaledBox_halfWidth, h₀]
    ring
  · change (scaledBox κ targetOffset b.target).halfWidth 1 =
      (scaledBox κ sourceOffset b.source).halfWidth 1 / (b.factor : ℝ)
    rw [scaledBox_halfWidth, scaledBox_halfWidth, h₁]
    ring

def embedPlane (κ : ℚ) (offset : Fin 2 → ℚ) (x : Plane) : Plane :=
  fun j => (offset j : ℝ) + (κ : ℝ) * x j

theorem scaledBox_image {κ : ℚ} (hκ : 0 < κ) (offset : Fin 2 → ℚ)
    (R : RationalBox 2) : embedPlane κ offset '' R.carrier = (scaledBox κ offset R).carrier := by
  have hp : (0 : ℝ) < κ := by exact_mod_cast hκ
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ j
    have hj := hx j
    simpa only [scaledBox, embedPlane, Rat.cast_add, Rat.cast_mul] using
      And.intro (add_le_add (le_refl (offset j : ℝ)) (mul_le_mul_of_nonneg_left hj.1 hp.le))
        (add_le_add (le_refl (offset j : ℝ)) (mul_le_mul_of_nonneg_left hj.2 hp.le))
  · intro hy
    let x : Plane := fun j => (y j - (offset j : ℝ)) / (κ : ℝ)
    refine ⟨x, ?_, ?_⟩
    · intro j
      have hj := hy j
      simp only [scaledBox, Rat.cast_add, Rat.cast_mul] at hj
      constructor
      · change (R.lower j : ℝ) ≤ (y j - (offset j : ℝ)) / (κ : ℝ)
        apply (le_div_iff₀ hp).mpr
        linarith [hj.1]
      · change (y j - (offset j : ℝ)) / (κ : ℝ) ≤ (R.upper j : ℝ)
        apply (div_le_iff₀ hp).mpr
        linarith [hj.2]
    · funext j
      dsimp [embedPlane, x]
      field_simp
      ring

theorem scaledInstruction_action (κ : ℚ) (sourceOffset targetOffset : Fin 2 → ℚ)
    (b : Instruction) (x : Plane) :
    (scaledInstruction κ sourceOffset targetOffset b).affine (embedPlane κ sourceOffset x) =
      embedPlane κ targetOffset (b.affine x) := by
  funext j
  fin_cases j <;>
    simp only [scaledInstruction, Instruction.affine, embedPlane, scaledBox_center] <;> dsimp <;> ring

end ForcedComputation.Radix

end

end OAI
