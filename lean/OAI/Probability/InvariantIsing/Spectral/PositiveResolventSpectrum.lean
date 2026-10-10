import OAI.Probability.InvariantIsing.Gaussian.HermitianGaussianQuadratic
import OAI.Probability.InvariantIsing.Gaussian.GaussianGramResolvent

namespace OAI

/-! Spectral bounds for the positive resolvents occurring after deletion of a column. -/
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

def positiveResolvent {N : ℕ} (t : ℝ) (B : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B)⁻¹

lemma positiveResolvent_posDef {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) : (positiveResolvent t B).PosDef :=
  ((Matrix.PosDef.one.smul ht).add_posSemidef hB).inv

lemma positiveResolvent_eigenvalues {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) (i : Fin N) :
    0 ≤ (positiveResolvent_posDef ht hB).isHermitian.eigenvalues i ∧
    (positiveResolvent_posDef ht hB).isHermitian.eigenvalues i ≤ 1/t := by
  let R := positiveResolvent t B
  let hR : R.PosDef := positiveResolvent_posDef ht hB
  let u := hR.isHermitian.eigenvectorBasis i
  let a := hR.isHermitian.eigenvalues i
  have hu : u.ofLp ⬝ᵥ u.ofLp = 1 := by
    change ⟪u,u⟫ = 1
    rw [real_inner_self_eq_norm_sq]
    simp only [u,hR.isHermitian.eigenvectorBasis.orthonormal.1 i,one_pow]
  have ha : 0 ≤ a := by
    dsimp only [a]
    rw [hR.isHermitian.eigenvalues_eq]
    simpa only [star_trivial,RCLike.re_to_real] using hR.posSemidef.dotProduct_mulVec_nonneg u.ofLp
  have hq : 0 ≤ u.ofLp ⬝ᵥ (B *ᵥ u.ofLp) := by
    simpa only [star_trivial] using hB.dotProduct_mulVec_nonneg u.ofLp
  have hinv : (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B)*R = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
      (((Matrix.PosDef.one.smul ht).add_posSemidef hB).det_pos.ne'))
  have heig : R *ᵥ u.ofLp = a • u.ofLp := hR.isHermitian.mulVec_eigenvectorBasis i
  have hh : (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B) *ᵥ (R *ᵥ u.ofLp) = u.ofLp := by
    rw [Matrix.mulVec_mulVec,hinv,Matrix.one_mulVec]
  rw [heig,Matrix.mulVec_smul,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec] at hh
  have hd := congrArg (fun y => u.ofLp ⬝ᵥ y) hh
  rw [dotProduct_smul,dotProduct_add,dotProduct_smul,hu] at hd
  simp only [smul_eq_mul,mul_one] at hd
  constructor
  · exact ha
  · apply (le_div_iff₀ ht).mpr
    nlinarith [mul_nonneg ha hq]

end InvariantIsing

end

end OAI
