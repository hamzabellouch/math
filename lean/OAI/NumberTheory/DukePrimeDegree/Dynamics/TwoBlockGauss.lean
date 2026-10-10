import OAI.NumberTheory.DukePrimeDegree.Dynamics.TwoBlockGroups

namespace OAI

/-!
# Actual two-block Gauss coordinates in the special linear group

An invertible principal block gives lower-cross, neutral, and upper-cross
factors. The neutral factor is constructed by multiplication inside SL,
so no separate determinant formula is postulated. These are the algebraic
coordinates for the singular-block chart; topology and conditional graph
transport are subsequent steps.
-/

noncomputable section
open Matrix
open scoped Classical

namespace DukePrimeDegree

def twoBlockUpperCoordinate {a b : ℕ} (g : TwoBlockSL a b) :
    Matrix (Fin a) (Fin b) ℝ :=
  g.val.toBlocks₁₁⁻¹ * g.val.toBlocks₁₂

def twoBlockLowerCoordinate {a b : ℕ} (g : TwoBlockSL a b) :
    Matrix (Fin b) (Fin a) ℝ :=
  g.val.toBlocks₂₁ * g.val.toBlocks₁₁⁻¹

def twoBlockCore {a b : ℕ} (g : TwoBlockSL a b) : TwoBlockSL a b :=
  twoBlockLower (-twoBlockLowerCoordinate g) * g *
    twoBlockUpper (-twoBlockUpperCoordinate g)

theorem twoBlockGauss_factorization {a b : ℕ} (g : TwoBlockSL a b) :
    g = twoBlockLower (twoBlockLowerCoordinate g) * twoBlockCore g *
      twoBlockUpper (twoBlockUpperCoordinate g) := by
  rw [twoBlockCore, ← twoBlockLower_inv, ← twoBlockUpper_inv]
  group

theorem twoBlockCore_matrix {a b : ℕ} (g : TwoBlockSL a b)
    (hA : IsUnit g.val.toBlocks₁₁) :
    (twoBlockCore g).val = Matrix.fromBlocks g.val.toBlocks₁₁ 0 0
      (g.val.toBlocks₂₂ - g.val.toBlocks₂₁ * g.val.toBlocks₁₁⁻¹ * g.val.toBlocks₁₂) := by
  let A := g.val.toBlocks₁₁
  let B := g.val.toBlocks₁₂
  let C := g.val.toBlocks₂₁
  let D := g.val.toBlocks₂₂
  let := hA.invertible
  have hCA : (C * A⁻¹) * A = C := by
    rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one]
  have hAB : A * (A⁻¹ * B) = B := by
    rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
  have hg : g.val = Matrix.fromBlocks A B C D := (Matrix.fromBlocks_toBlocks g.val).symm
  change Matrix.fromBlocks 1 0 (-(C * A⁻¹)) 1 * g.val *
    Matrix.fromBlocks 1 (-(A⁻¹ * B)) 0 1 = Matrix.fromBlocks A 0 0 (D - C * A⁻¹ * B)
  rw [hg]
  simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, Matrix.neg_mul,
    Matrix.mul_neg, hCA, neg_add_cancel, hAB, sub_eq_add_neg, neg_zero, zero_add]
  congr 1
  exact add_comm _ _

theorem twoBlockCore_mem_neutral {a b : ℕ} (g : TwoBlockSL a b)
    (hA : IsUnit g.val.toBlocks₁₁) :
    twoBlockCore g ∈ twoBlockNeutralGroup a b := by
  rw [mem_twoBlockNeutralGroup_iff, twoBlockCore_matrix g hA]
  exact ⟨Matrix.toBlocks_fromBlocks₁₂ _ _ _ _, Matrix.toBlocks_fromBlocks₂₁ _ _ _ _⟩

lemma isUnit_principal_of_twoBlockNeutral {a b : ℕ}
    (g : twoBlockNeutralGroup a b) : IsUnit g.val.val.toBlocks₁₁ := by
  have hzero := (mem_twoBlockNeutralGroup_iff g.val).mp g.property
  have hunit : IsUnit g.val.val := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [g.val.property]
    exact isUnit_one)
  have hg : g.val.val = Matrix.fromBlocks g.val.val.toBlocks₁₁ 0 0
      g.val.val.toBlocks₂₂ := by
    simpa only [hzero.1, hzero.2] using (Matrix.fromBlocks_toBlocks g.val.val).symm
  rw [hg] at hunit
  exact (Matrix.isUnit_fromBlocks_zero₂₁.mp hunit).1

lemma twoBlock_product_matrix {a b : ℕ}
    (L : Matrix (Fin b) (Fin a) ℝ) (C : twoBlockNeutralGroup a b)
    (U : Matrix (Fin a) (Fin b) ℝ) :
    (twoBlockLower L * C.val * twoBlockUpper U).val =
      Matrix.fromBlocks C.val.val.toBlocks₁₁ (C.val.val.toBlocks₁₁ * U)
        (L * C.val.val.toBlocks₁₁)
        (L * C.val.val.toBlocks₁₁ * U + C.val.val.toBlocks₂₂) := by
  have hzero := (mem_twoBlockNeutralGroup_iff C.val).mp C.property
  have hC : C.val.val = Matrix.fromBlocks C.val.val.toBlocks₁₁ 0 0
      C.val.val.toBlocks₂₂ := by
    simpa only [hzero.1, hzero.2] using (Matrix.fromBlocks_toBlocks C.val.val).symm
  change Matrix.fromBlocks 1 0 L 1 * C.val.val * Matrix.fromBlocks 1 U 0 1 = _
  rw [hC]
  simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂]

theorem twoBlockGauss_coordinates_product {a b : ℕ}
    (L : Matrix (Fin b) (Fin a) ℝ) (C : twoBlockNeutralGroup a b)
    (U : Matrix (Fin a) (Fin b) ℝ) :
    twoBlockLowerCoordinate (twoBlockLower L * C.val * twoBlockUpper U) = L ∧
      twoBlockUpperCoordinate (twoBlockLower L * C.val * twoBlockUpper U) = U := by
  let := (isUnit_principal_of_twoBlockNeutral C).invertible
  have hlow : (L * C.val.val.toBlocks₁₁) * C.val.val.toBlocks₁₁⁻¹ = L := by
    rw [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]
  have hupp : C.val.val.toBlocks₁₁⁻¹ * (C.val.val.toBlocks₁₁ * U) = U := by
    rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul]
  simp only [twoBlockLowerCoordinate, twoBlockUpperCoordinate, twoBlock_product_matrix,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁]
  exact ⟨hlow, hupp⟩

lemma twoBlock_product_principal_isUnit {a b : ℕ}
    (L : Matrix (Fin b) (Fin a) ℝ) (C : twoBlockNeutralGroup a b)
    (U : Matrix (Fin a) (Fin b) ℝ) :
    IsUnit (twoBlockLower L * C.val * twoBlockUpper U).val.toBlocks₁₁ := by
  simpa only [twoBlock_product_matrix, Matrix.toBlocks_fromBlocks₁₁] using
    isUnit_principal_of_twoBlockNeutral C

theorem twoBlockCore_product {a b : ℕ}
    (L : Matrix (Fin b) (Fin a) ℝ) (C : twoBlockNeutralGroup a b)
    (U : Matrix (Fin a) (Fin b) ℝ) :
    twoBlockCore (twoBlockLower L * C.val * twoBlockUpper U) = C.val := by
  have hcoord := twoBlockGauss_coordinates_product L C U
  rw [twoBlockCore, hcoord.1, hcoord.2, ← twoBlockLower_inv, ← twoBlockUpper_inv]
  group

end DukePrimeDegree

end

end OAI
