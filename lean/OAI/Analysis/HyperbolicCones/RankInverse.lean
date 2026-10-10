import OAI.Analysis.HyperbolicCones.RankNorm
import OAI.Analysis.HyperbolicCones.KernelLimit

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem rankOne_path_eq_affine {n : ℕ} (v : Vec n) (t : ℝ) :
    outerSym v + t • (1 - outerSym v) = 1 + (t - 1) • (1 - outerSym v) := by
  module

theorem rankOne_path_inverse {n : ℕ} (v : Vec n) (hv : ‖v‖ = 1)
    (t : ℝ) (ht : t ≠ 0) :
    (outer v + t • (1 - outer v))⁻¹ = outer v + t⁻¹ • (1 - outer v) := by
  apply Matrix.inv_eq_left_inv
  have hp := outer_isStarProjection v hv
  rw [add_mul, mul_add, mul_add, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    hp.isIdempotentElem, hp.mul_one_sub_self, hp.one_sub_mul_self,
    hp.one_sub.isIdempotentElem]
  simp [mul_inv_cancel₀ ht]

theorem rankOne_path_inverseSquareRoot {n : ℕ} (v : Vec n) (hv : ‖v‖ = 1)
    (t : ℝ) :
    inverseSquareRoot (outerSym v + t • (1 - outerSym v)) =
      outer v + (Real.sqrt t)⁻¹ • (1 - outer v) := by
  rw [rankOne_path_eq_affine, inverseSquareRoot_affine_eq_cfc]
  let H : Sym n := 1 - outerSym v
  have hidem : IsIdempotentElem (H : Mat n ℝ) :=
    (outer_isStarProjection v hv).one_sub.isIdempotentElem
  have hspec : spectrum ℝ (H : Mat n ℝ) ⊆ {0, 1} :=
    (isIdempotentElem_iff_spectrum_subset ℝ (H : Mat n ℝ) H.property).mp hidem
  change cfc (fun x : ℝ => (Real.sqrt (1 + (t - 1) * x))⁻¹) (H : Mat n ℝ) = _
  calc
    _ = cfc (fun x : ℝ => 1 + ((Real.sqrt t)⁻¹ - 1) * x) (H : Mat n ℝ) := by
      apply cfc_congr
      intro x hx
      have hx' : x = 0 ∨ x = 1 := by simpa using hspec hx
      rcases hx' with rfl | rfl <;> simp
    _ = 1 • (1 : Mat n ℝ) + ((Real.sqrt t)⁻¹ - 1) • (H : Mat n ℝ) :=
      matrix_cfc_affine H 1 ((Real.sqrt t)⁻¹ - 1)
    _ = outer v + (Real.sqrt t)⁻¹ • (1 - outer v) := by
      dsimp [H, outerSym]
      module

end Paper256

end

end OAI
