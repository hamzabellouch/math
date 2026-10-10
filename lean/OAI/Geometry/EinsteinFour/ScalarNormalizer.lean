import OAI.Geometry.EinsteinFour.ScalarDirichlet
import Mathlib.Analysis.Matrix.Order

namespace OAI

/-! The positive scalar normalizer used in finite radial compression. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix
open scoped MatrixOrder

noncomputable section

def scalarNormalizer {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  CFC.sqrt L⁻¹

theorem scalarNormalizer_posSemidef {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) :
    (scalarNormalizer L).PosSemidef := (CFC.sqrt_nonneg L⁻¹).posSemidef

theorem scalarNormalizer_square {N : ℕ} {L : Matrix (Fin N) (Fin N) ℝ} (hL : L.PosDef) :
    scalarNormalizer L * scalarNormalizer L = L⁻¹ :=
  CFC.sqrt_mul_sqrt_self L⁻¹ hL.inv.posSemidef.nonneg

theorem scalarNormalizer_normalizes {N : ℕ} {L : Matrix (Fin N) (Fin N) ℝ} (hL : L.PosDef) :
    scalarNormalizer L * L * scalarNormalizer L = 1 := by
  have hsq := scalarNormalizer_square hL
  have ht : scalarNormalizer L * (scalarNormalizer L * L) = 1 := by
    rw [← Matrix.mul_assoc, hsq,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hL.isUnit)]
  exact mul_eq_one_comm.mp ht

theorem positive_square_root_eigenvector {N : ℕ}
    {G : Matrix (Fin N) (Fin N) ℝ} {w : Fin N → ℝ} {c : ℝ}
    (hG : G.PosSemidef) (hc : 0 < c)
    (heigen : (G * G) *ᵥ w = c ^ 2 • w) :
    G *ᵥ w = c • w := by
  have hK : (G + c • (1 : Matrix (Fin N) (Fin N) ℝ)).PosDef :=
    Matrix.PosDef.posSemidef_add hG (Matrix.PosDef.one.smul hc)
  let z := G *ᵥ w - c • w
  have hz : (G + c • (1 : Matrix (Fin N) (Fin N) ℝ)) *ᵥ z = 0 := by
    dsimp [z]
    simp only [Matrix.add_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [Matrix.mulVec_mulVec, heigen]
    module
  have hz0 : z = 0 := (Matrix.mulVec_injective_of_isUnit hK.isUnit)
    (by simpa only [Matrix.mulVec_zero] using hz)
  exact sub_eq_zero.mp hz0

/-- The normalizer acts by the reciprocal square root on the prescribed
positive scalar eigenmode. -/
theorem scalarNormalizer_eigenvector {N : ℕ}
    {L : Matrix (Fin N) (Fin N) ℝ} (hL : L.PosDef)
    {w : Fin N → ℝ} {lam : ℝ} (hlam : 0 < lam) (heigen : L *ᵥ w = lam • w) :
    scalarNormalizer L *ᵥ w = (1 / Real.sqrt lam) • w := by
  have hi : L⁻¹ *ᵥ w = (1 / lam) • w := by
    have h := congrArg (fun x => L⁻¹ *ᵥ x) heigen
    rw [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hL.isUnit),
      Matrix.one_mulVec, Matrix.mulVec_smul] at h
    calc
      _ = (1 / lam) • (lam • (L⁻¹ *ᵥ w)) := by
        rw [smul_smul, one_div_mul_cancel hlam.ne', one_smul]
      _ = _ := by rw [← h]
  apply positive_square_root_eigenvector (scalarNormalizer_posSemidef L)
    (one_div_pos.mpr (Real.sqrt_pos.mpr hlam))
  rw [scalarNormalizer_square hL, hi]
  congr 1
  rw [div_pow, one_pow, Real.sq_sqrt hlam.le]

end

end PositiveEinsteinFour.Jacobi

end OAI
