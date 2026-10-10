import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiCutoffAlgebra
import OAI.Geometry.PrescribedPotential.CalabiPointInequalities
import OAI.Geometry.PrescribedPotential.CalabiRescue
import OAI.Geometry.PrescribedPotential.CalabiResidualBound
import OAI.Geometry.PrescribedPotential.PotentialLinearCalculus
import OAI.Geometry.PrescribedPotential.ScalarProductLaplacian

namespace OAI

/-! Calabi Cutoff Point. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus.LocalKaehlerField
variable {n : ℕ} (K : LocalKaehlerField n)

lemma calabi_cutoff_max_at_one {z : V n} (hz : z ∈ K.domain) (hM : K.matrix z = 1)
    (D : Matrix (Fin n) (Fin n) ℂ) {η : V n → ℝ} (hηs : ContDiffAt ℝ ∞ η z)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hη : 0 ≤ η z) (hη1 : η z ≤ 1)
    (hηlap : -C ≤ (PotentialKaehler.potentialMatrix η z).trace.re)
    (hηgrad : holGradientSquare η z ≤ C*η z)
    (hRes : -C*(1+K.calabiNorm z) ≤ calabiResidual (K.ricciHessian z)
      (fun i => mderiv (-Complex.I) (e i) K.ricciHessian z) (fun i => K.connection i z))
    (hRic : -C ≤ (Dᴴ*K.ricciHessian z*D).trace.re)
    (hRescue : δ*K.calabiNorm z ≤ rescueSquare D (fun i => K.connection i z))
    (hmax : IsLocalMax (fun y => η y*K.calabiNorm y+((6*C+1)/δ)*K.weightedTrace D y) z) :
    K.calabiNorm z ≤ C*(1+(6*C+1)/δ) := by
  have hn := K.isOpen.mem_nhds hz
  have hSs := K.calabiNorm_smooth.contDiffAt hn
  have hTs := (K.weightedTrace_smooth D).contDiffAt hn
  have hS : 0 ≤ K.calabiNorm z := by rw [K.calabiNorm_at_one hM]; exact tensorSquare_nonneg _
  have hQ := K.calabiGood_nonneg z
  have hgrad : holGradientSquare K.calabiNorm z ≤ 2*K.calabiNorm z*K.calabiGood z := by
    rw [holGradientSquare_eq]
    exact K.calabi_gradient_sum_at_one hz hM
  have hcross : (gradientCross η K.calabiNorm z)^2 ≤ 8*C*η z*K.calabiNorm z*K.calabiGood z := by
    have hh := gradientCross_sq η K.calabiNorm z
    have ha := mul_le_mul hηgrad hgrad (sq_nonneg ‖holGradient K.calabiNorm z‖)
      (mul_nonneg hC hη)
    dsimp only [holGradientSquare] at ha hh
    nlinarith
  have hLS : K.calabiGood z-C*(1+K.calabiNorm z) ≤
      (PotentialKaehler.potentialMatrix K.calabiNorm z).trace.re := by
    rw [K.calabi_bochner_real_at_one hz hM]
    linarith
  have hLT : δ*K.calabiNorm z-C ≤
      (PotentialKaehler.potentialMatrix (K.weightedTrace D) z).trace.re := by
    rw [K.weightedTrace_laplacian_at_one D hz hM]
    linarith
  have ht := EllipticKernel.trace_potentialMatrix_nonpos_at_localMax
    ((hηs.mul hSs).add (contDiffAt_const.mul hTs)) hmax (1 : Matrix (Fin n) (Fin n) ℂ) Matrix.PosDef.one
  rw [inv_one,one_mul,potentialMatrix_affine (hηs.mul hSs) hTs,Matrix.trace_add,Matrix.trace_smul,
    Complex.add_re] at ht
  simp only [smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at ht
  rw [potentialMatrix_trace_mul hηs hSs] at ht
  exact CalabiEstimate.cutoff_max_bound hS hQ hη hη1 hC hδ hLS hLT hηlap hcross ht
end KaehlerCalculus.LocalKaehlerField

end
end

end OAI
