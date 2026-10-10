import OAI.Probability.InvariantIsing.Spectral.PositiveResolventSpectrum
import Mathlib.Analysis.InnerProductSpace.Trace

namespace OAI

/-! The positive resolvent in the eigenbasis of the original positive matrix. -/
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma positiveResolvent_eigenvector {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) (i : Fin N) :
    (positiveResolvent t B).toEuclideanLin (hB.isHermitian.eigenvectorBasis i) =
      (t+hB.isHermitian.eigenvalues i)⁻¹ • hB.isHermitian.eigenvectorBasis i := by
  let u := (hB.isHermitian.eigenvectorBasis i).ofLp
  let a := hB.isHermitian.eigenvalues i
  have ha : 0 < t+a := add_pos_of_pos_of_nonneg ht (hB.eigenvalues_nonneg i)
  have hBu : B *ᵥ u = a • u := hB.isHermitian.mulVec_eigenvectorBasis i
  have hAu : (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B) *ᵥ u = (t+a) • u := by
    rw [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,hBu,add_smul]
  have hinv : positiveResolvent t B*(t • (1 : Matrix (Fin N) (Fin N) ℝ)+B) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (((Matrix.PosDef.one.smul ht).add_posSemidef hB).det_pos.ne'))
  have hh : (t+a) • (positiveResolvent t B *ᵥ u) = u := by
    rw [← Matrix.mulVec_smul,← hAu,Matrix.mulVec_mulVec,hinv,Matrix.one_mulVec]
  have hu : positiveResolvent t B *ᵥ u = (t+a)⁻¹ • u := by
    calc
      _ = (t+a)⁻¹ • ((t+a) • (positiveResolvent t B *ᵥ u)) := by
        rw [smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
      _ = _ := by rw [hh]
  ext j
  exact congrFun hu j

lemma positiveResolvent_trace_eigenvalues {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) :
    (positiveResolvent t B).trace = ∑ i, (t+hB.isHermitian.eigenvalues i)⁻¹ := by
  have htr := LinearMap.trace_eq_sum_inner (positiveResolvent t B).toEuclideanLin hB.isHermitian.eigenvectorBasis
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,Matrix.trace_toLin_eq] at htr
  rw [htr]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [positiveResolvent_eigenvector ht hB,real_inner_smul_right,real_inner_self_eq_norm_sq]
  simp only [hB.isHermitian.eigenvectorBasis.orthonormal.1 i,one_pow,mul_one]

end InvariantIsing

end

end OAI
