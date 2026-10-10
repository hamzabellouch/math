import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiBochner
import OAI.Geometry.PrescribedPotential.CalabiFrameAlgebra
import OAI.Geometry.PrescribedPotential.HolomorphicDirection
import OAI.Geometry.PrescribedPotential.MatrixFrameNormalization
import OAI.Geometry.PrescribedPotential.ScalarFrameCalculus

namespace OAI

/-! Calabi Frame Calculus. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus.LocalKaehlerField
variable {n : ℕ} (K : LocalKaehlerField n)

def pull (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B)) : LocalKaehlerField n where
  domain := B ⁻¹' K.domain
  isOpen := K.isOpen.preimage B.continuous
  matrix := pullMetric B K.matrix
  smooth := pullMetric_smooth K.isOpen B K.smooth
  positive := pullMetric_positive B hB K.positive
  closed := pullMetric_closed K.isOpen B K.smooth K.closed

lemma pull_connection (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B))
    {w : V n} (hw : B w ∈ K.domain) (i : Fin n) :
    (K.pull B hB).connection i w = pullConnectionTensor (frameMatrix B) (fun p => K.connection p (B w)) i := by
  let C := frameMatrix B
  have hc : C*C⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hB)
  have hd : (Cᴴ)⁻¹*Cᴴ = 1 := by
    rw [← Matrix.conjTranspose_nonsing_inv,← Matrix.conjTranspose_mul,hc,Matrix.conjTranspose_one]
  change (pullMetric B K.matrix w)⁻¹*mderiv (-Complex.I) (e i) (pullMetric B K.matrix) w = _
  rw [mderiv_pullMetric B (K.smooth.contDiffAt (K.isOpen.mem_nhds hw))]
  unfold pullMetric
  change (Cᴴ*K.matrix (B w)*C)⁻¹*(Cᴴ*mderiv (-Complex.I) (B (e i)) K.matrix (B w)*C) = _
  simp only [Matrix.mul_inv_rev,mul_assoc]
  rw [← mul_assoc (Cᴴ)⁻¹ Cᴴ,hd,one_mul,mderiv_hol_coordinates]
  have he (p) : B (e i) p = C p i := rfl
  simp only [he,pullConnectionTensor,connection,Matrix.mul_sum,Matrix.mul_smul,Matrix.sum_mul,Matrix.smul_mul,mul_assoc,C]

lemma pull_calabiNorm (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B))
    {w : V n} (hw : B w ∈ K.domain) :
    (K.pull B hB).calabiNorm w = K.calabiNorm (B w) := by
  unfold calabiNorm tensorPair
  simp_rw [K.pull_connection B hB hw]
  change (tensorPairAt (pullMetric B K.matrix w)⁻¹ (pullMetric B K.matrix w) _ _).re = _
  unfold pullMetric
  simp only [Matrix.mul_inv_rev]
  exact congrArg Complex.re (by
    simpa only [mul_assoc] using tensorPairAt_changeBasis (frameMatrix B) (K.matrix (B w))⁻¹
      (K.matrix (B w)) hB (fun p => K.connection p (B w)) (fun p => K.connection p (B w)))

lemma pull_ricciHessian (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B))
    {w : V n} (hw : B w ∈ K.domain) :
    (K.pull B hB).ricciHessian w = pullMetric B K.ricciHessian w :=
  potentialMatrix_logdet_pullMetric K.isOpen B hB K.smooth K.positive hw

lemma pull_ricciHessian_hol (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B))
    {w : V n} (hw : B w ∈ K.domain) (i : Fin n) :
    mderiv (-Complex.I) (e i) (K.pull B hB).ricciHessian w =
      (frameMatrix B)ᴴ * mderiv (-Complex.I) (B (e i)) K.ricciHessian (B w) * frameMatrix B := by
  have he : (K.pull B hB).ricciHessian =ᶠ[𝓝 w] pullMetric B K.ricciHessian := by
    filter_upwards [B.continuous.continuousAt.preimage_mem_nhds (K.isOpen.mem_nhds hw)] with y hy
    exact K.pull_ricciHessian B hB hy
  rw [mderiv_congr he]
  exact mderiv_pullMetric B (K.ricciHessian_smooth.contDiffAt (K.isOpen.mem_nhds hw)) _ _
end KaehlerCalculus.LocalKaehlerField

end
end

end OAI
