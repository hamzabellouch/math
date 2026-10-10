import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-!
# The two cross-block groups and the neutral block group

These are concrete subgroups of the same determinant-one matrix group.
The rectangular cross-block coordinates are additive, and the neutral
group is the centralizer of the coordinate projection. This supplies
the group side of the singular two-block chart, without an entropy or
measure-classification assumption.
-/

noncomputable section
open Matrix
open scoped Classical

namespace DukePrimeDegree

abbrev TwoBlockSL (a b : ℕ) :=
  Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) ℝ

def twoBlockProjection (a b : ℕ) :
    Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ :=
  Matrix.fromBlocks 1 0 0 0

def twoBlockUpper {a b : ℕ} (U : Matrix (Fin a) (Fin b) ℝ) : TwoBlockSL a b :=
  ⟨Matrix.fromBlocks 1 U 0 1, by rw [Matrix.det_fromBlocks_zero₂₁]; simp⟩

def twoBlockLower {a b : ℕ} (U : Matrix (Fin b) (Fin a) ℝ) : TwoBlockSL a b :=
  ⟨Matrix.fromBlocks 1 0 U 1, by rw [Matrix.det_fromBlocks_zero₁₂]; simp⟩

@[simp] lemma twoBlockUpper_zero (a b : ℕ) :
    twoBlockUpper (0 : Matrix (Fin a) (Fin b) ℝ) = 1 := by
  apply Subtype.ext
  exact Matrix.fromBlocks_one

@[simp] lemma twoBlockLower_zero (a b : ℕ) :
    twoBlockLower (0 : Matrix (Fin b) (Fin a) ℝ) = 1 := by
  apply Subtype.ext
  exact Matrix.fromBlocks_one

lemma twoBlockUpper_add {a b : ℕ} (U V : Matrix (Fin a) (Fin b) ℝ) :
    twoBlockUpper (U + V) = twoBlockUpper U * twoBlockUpper V := by
  apply Subtype.ext
  change Matrix.fromBlocks 1 (U + V) 0 1 =
    Matrix.fromBlocks 1 U 0 1 * Matrix.fromBlocks 1 V 0 1
  simp only [Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    add_comm V U]

lemma twoBlockLower_add {a b : ℕ} (U V : Matrix (Fin b) (Fin a) ℝ) :
    twoBlockLower (U + V) = twoBlockLower U * twoBlockLower V := by
  apply Subtype.ext
  change Matrix.fromBlocks 1 0 (U + V) 1 =
    Matrix.fromBlocks 1 0 U 1 * Matrix.fromBlocks 1 0 V 1
  simp only [Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]

@[simp] lemma twoBlockUpper_inv {a b : ℕ} (U : Matrix (Fin a) (Fin b) ℝ) :
    (twoBlockUpper U)⁻¹ = twoBlockUpper (-U) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← twoBlockUpper_add, add_neg_cancel, twoBlockUpper_zero]

@[simp] lemma twoBlockLower_inv {a b : ℕ} (U : Matrix (Fin b) (Fin a) ℝ) :
    (twoBlockLower U)⁻¹ = twoBlockLower (-U) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← twoBlockLower_add, add_neg_cancel, twoBlockLower_zero]

/-- The block-diagonal determinant-one subgroup, expressed without a
choice of bases in either block beyond the fixed coordinates. -/
def twoBlockNeutralGroup (a b : ℕ) : Subgroup (TwoBlockSL a b) where
  carrier := {g | g.val * twoBlockProjection a b = twoBlockProjection a b * g.val}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (g.val * h.val) * _ = _ * (g.val * h.val)
    calc
      (g.val * h.val) * twoBlockProjection a b =
          g.val * (h.val * twoBlockProjection a b) := mul_assoc _ _ _
      _ = g.val * (twoBlockProjection a b * h.val) := by rw [hh]
      _ = (g.val * twoBlockProjection a b) * h.val := (mul_assoc _ _ _).symm
      _ = (twoBlockProjection a b * g.val) * h.val := by rw [hg]
      _ = twoBlockProjection a b * (g.val * h.val) := mul_assoc _ _ _
  inv_mem' := by
    intro g hg
    have he := congrArg (fun M => g⁻¹.val * M * g⁻¹.val) hg
    have hleft : g⁻¹.val * g.val = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hright : g.val * g⁻¹.val = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hleftP : g⁻¹.val * (g.val * twoBlockProjection a b) =
        twoBlockProjection a b := by
      rw [← mul_assoc, hleft, one_mul]
    change g⁻¹.val * _ = _ * g⁻¹.val
    simpa only [hleftP, mul_assoc, hright, mul_one] using he.symm

lemma mem_twoBlockNeutralGroup_iff {a b : ℕ} (g : TwoBlockSL a b) :
    g ∈ twoBlockNeutralGroup a b ↔
      g.val.toBlocks₁₂ = 0 ∧ g.val.toBlocks₂₁ = 0 := by
  change g.val * twoBlockProjection a b = twoBlockProjection a b * g.val ↔ _
  rw [← Matrix.fromBlocks_toBlocks g.val]
  simp only [twoBlockProjection, Matrix.fromBlocks_multiply, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero,
    Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁]
  constructor
  · intro h
    constructor
    · have he := congrArg Matrix.toBlocks₁₂ h
      simpa only [Matrix.toBlocks_fromBlocks₁₂] using he.symm
    · have he := congrArg Matrix.toBlocks₂₁ h
      simpa only [Matrix.toBlocks_fromBlocks₂₁] using he
  · rintro ⟨hU, hL⟩
    rw [hU, hL]

end DukePrimeDegree

end

end OAI
