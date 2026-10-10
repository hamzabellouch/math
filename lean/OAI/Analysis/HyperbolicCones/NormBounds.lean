import OAI.Analysis.HyperbolicCones.NormCongruence
import OAI.Analysis.HyperbolicCones.NormLimits

namespace OAI

/-! The positivity bounds and individual scalar rays in the proof of the norm identity. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace Paper256

theorem affine_ge_one {n : ℕ} (H : Sym n) (hH : (H : Mat n ℝ).PosSemidef)
    (t : ℝ) (ht : 1 ≤ t) :
    (1 : Mat n ℝ) ≤ ((1 + (t - 1) • H : Sym n) : Mat n ℝ) := by
  change (1 : Mat n ℝ) ≤ 1 + (t - 1) • (H : Mat n ℝ)
  exact le_add_of_nonneg_right ((hH.smul (sub_nonneg.mpr ht)).nonneg)

theorem positive_unital_map_affine_ge_one {m n : ℕ} (D : Sym m →ₗ[ℝ] Sym n)
    (hD : ∀ H : Sym m, (H : Mat m ℝ).PosSemidef → (D H : Mat n ℝ).PosSemidef)
    (hI : D 1 = 1) (H : Sym m) (hH : (H : Mat m ℝ).PosSemidef)
    (t : ℝ) (ht : 1 ≤ t) :
    (1 : Mat n ℝ) ≤ (D (1 + (t - 1) • H) : Mat n ℝ) := by
  simpa only [map_add, map_smul, hI] using affine_ge_one (D H) (hD H hH) t ht

theorem whitened_phi_posSemidef (X Z : Sym 4) (hX : (X : Mat 4 ℝ).PosDef)
    (y : Fin 3 → ℝ) :
    (inverseSquareRoot Z * phi y (X : Mat 4 ℝ)⁻¹ * inverseSquareRoot Z).PosSemidef := by
  have h := (phi_posSemidef y _ hX.inv.posSemidef).conjTranspose_mul_mul_same
    (inverseSquareRoot Z)
  simpa only [conjTranspose_eq_transpose_of_trivial, inverseSquareRoot_transpose] using h

theorem whitened_phi_threshold (X Z : Sym 4) (hX : (X : Mat 4 ℝ).PosDef)
    (hZ : (Z : Mat 4 ℝ).PosDef) (y : Fin 3 → ℝ) (r : ℝ) :
    (r • (Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef ↔
      ‖inverseSquareRoot Z * phi y (X : Mat 4 ℝ)⁻¹ * inverseSquareRoot Z‖ ≤ r := by
  rw [inverseSquareRoot_congruence Z hZ]
  exact posSemidef_norm_threshold _ (whitened_phi_posSemidef X Z hX y) r

end Paper256

end

end OAI
