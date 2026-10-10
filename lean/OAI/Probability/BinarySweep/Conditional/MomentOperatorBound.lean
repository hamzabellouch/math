import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.SchattenTriangle
import OAI.Probability.BinarySweep.FiniteLaws.HilbertMainCases

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Classical

namespace BinaryCoordinateSweeps
open TraceHolder Irrep

lemma norm_le_momentRoot {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (hq : 0<q) (A : M ι) :
    ‖A‖ ≤ matrixMoment q A ^ (((2*q:ℕ):ℝ)⁻¹) := by
  exact norm_le_schatten hq A

lemma norm_le_traceMomentRoot {D q : ℕ} (hq : 0<q)
    (K : RepSpace D →L[ℂ] RepSpace D) :
    ‖K‖≤traceMoment q K ^ (((2*q:ℕ):ℝ)⁻¹) := by
  let v := EuclideanSpace.basisFun (Fin D) ℂ
  let A := LinearMap.toMatrixOrthonormal v K.toLinearMap
  have he : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin D)) A=K := by
    apply ContinuousLinearMap.coe_injective
    change (LinearMap.toMatrixOrthonormal v).symm
      (LinearMap.toMatrixOrthonormal v K.toLinearMap) = K.toLinearMap
    exact StarAlgEquiv.symm_apply_apply _ _
  have hm : traceMoment q K=matrixMoment q A := by
    have hh := evenMoment_orthonormalMatrix v q K.toLinearMap
    simpa only [traceMoment,evenMoment,ContinuousLinearMap.toLinearMap_pow,
      ContinuousLinearMap.toLinearMap_mul,ContinuousLinearMap.adjoint_toLinearMap] using hh
  rw [hm,←he,Matrix.l2_opNorm_toEuclideanCLM]
  exact norm_le_momentRoot hq A

lemma opNorm_of_logMoment {D q : ℕ} (hq : 0<q) (K : RepSpace D →L[ℂ] RepSpace D)
    {a : ℝ} (h : logMoment (traceMoment q K)≤(a:EReal)) :
    ‖K‖≤Real.exp (a/(2*q)) := by
  have ht := (logMoment_le_iff_le_exp _ _).mp h
  have hm := (norm_le_traceMomentRoot hq K).trans
    (Real.rpow_le_rpow (by
      have hh := evenMoment_nonneg q K.toLinearMap
      simpa only [traceMoment,evenMoment,ContinuousLinearMap.toLinearMap_pow,
        ContinuousLinearMap.toLinearMap_mul,ContinuousLinearMap.adjoint_toLinearMap] using hh) ht (by positivity))
  rw [← Real.exp_mul] at hm
  simpa only [Nat.cast_mul,Nat.cast_ofNat,div_eq_mul_inv] using hm

end BinaryCoordinateSweeps

end

end OAI
