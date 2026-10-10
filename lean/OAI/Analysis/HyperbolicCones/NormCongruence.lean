import OAI.Analysis.HyperbolicCones.NormThreshold

namespace OAI

/-! The scalar Schur thresholds are preserved by inverse-square-root congruence. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace Paper256

theorem inverseSquareRoot_congruence {n : ℕ} (Z : Sym n)
    (hZ : (Z : Mat n ℝ).PosDef) (F : Mat n ℝ) (r : ℝ) :
    (r • (Z : Mat n ℝ) - F).PosSemidef ↔
      (r • (1 : Mat n ℝ) - inverseSquareRoot Z * F * inverseSquareRoot Z).PosSemidef := by
  have heq : (inverseSquareRoot Z)ᵀ * (r • (Z : Mat n ℝ) - F) *
      inverseSquareRoot Z =
      r • (1 : Mat n ℝ) - inverseSquareRoot Z * F * inverseSquareRoot Z := by
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      inverseSquareRoot_conjugate Z hZ, inverseSquareRoot_transpose]
  have hc := (inverseSquareRoot_isUnit Z hZ).posSemidef_star_left_conjugate_iff
    (x := r • (Z : Mat n ℝ) - F)
  simpa only [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, heq] using hc.symm

theorem inverseSquareRoot_gram {m n : ℕ} (X : Sym m) (Z : Sym n)
    (hX : (X : Mat m ℝ).PosDef) (B : Matrix (Fin m) (Fin n) ℝ) :
    (inverseSquareRoot X * B * inverseSquareRoot Z)ᵀ *
        (inverseSquareRoot X * B * inverseSquareRoot Z) =
      inverseSquareRoot Z * (Bᵀ * (X : Mat m ℝ)⁻¹ * B) * inverseSquareRoot Z := by
  rw [transpose_mul, transpose_mul, inverseSquareRoot_transpose,
    inverseSquareRoot_transpose, ← inverseSquareRoot_sq X hX]
  simp only [Matrix.mul_assoc]

theorem NormalizedPencil.positive_threshold (P : NormalizedPencil)
    (X Z : Sym 4) (y : Fin 3 → ℝ)
    (hX : (X : Mat 4 ℝ).PosDef) (hZ : (Z : Mat 4 ℝ).PosDef)
    (hDX : (P.D X : Mat P.a ℝ).PosDef) (hEZ : (P.E Z : Mat P.c ℝ).PosDef) :
    ‖inverseSquareRoot Z * phi y (X : Mat 4 ℝ)⁻¹ * inverseSquareRoot Z‖ =
      ‖inverseSquareRoot (P.D X) * P.B y * inverseSquareRoot (P.E Z)‖ ^ 2 := by
  let : NeZero P.c := ⟨Nat.ne_of_gt P.c_pos⟩
  let A := inverseSquareRoot Z * phi y (X : Mat 4 ℝ)⁻¹ * inverseSquareRoot Z
  let C := inverseSquareRoot (P.D X) * P.B y * inverseSquareRoot (P.E Z)
  have hA : A.PosSemidef := by
    have hp := (phi_posSemidef y _ hX.inv.posSemidef).conjTranspose_mul_mul_same
      (inverseSquareRoot Z)
    simpa only [conjTranspose_eq_transpose_of_trivial, inverseSquareRoot_transpose] using hp
  have hr (r : ℝ) : ‖A‖ ≤ r ↔ ‖C‖ ^ 2 ≤ r := by
    calc
      _ ↔ (r • (1 : Mat 4 ℝ) - A).PosSemidef := (posSemidef_norm_threshold A hA r).symm
      _ ↔ (r • (Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef :=
        (inverseSquareRoot_congruence Z hZ _ r).symm
      _ ↔ ((P.E (r • Z) : Mat P.c ℝ) - (P.B y)ᵀ *
          (P.D X : Mat P.a ℝ)⁻¹ * P.B y).PosSemidef := by
        simpa only [selfAdjoint.val_smul] using P.schur_equivalence X (r • Z) y hX
      _ ↔ (r • (1 : Mat P.c ℝ) - Cᵀ * C).PosSemidef := by
        have hc := inverseSquareRoot_congruence (P.E Z) hEZ
          ((P.B y)ᵀ * (P.D X : Mat P.a ℝ)⁻¹ * P.B y) r
        simpa only [map_smul, selfAdjoint.val_smul, ← inverseSquareRoot_gram (P.D X) (P.E Z) hDX] using hc
      _ ↔ ‖C‖ ^ 2 ≤ r := posSemidef_gram_threshold C r
  exact le_antisymm ((hr _).mpr le_rfl) ((hr _).mp le_rfl)

end Paper256

end

end OAI
