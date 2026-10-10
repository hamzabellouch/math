import Mathlib
import OAI.Geometry.PrescribedPotential.WirtingerCalculus

namespace OAI

/-! Potential Linear Calculus. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma potentialMatrix_affine {f g : V n → ℝ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) (a : ℝ) :
    PotentialKaehler.potentialMatrix (fun y => f y+a*g y) z =
      PotentialKaehler.potentialMatrix f z+(a:ℂ) • PotentialKaehler.potentialMatrix g z := by
  have he := EllipticKernel.hessian_add_smul_sub_const hf hg a 0
  simp only [sub_zero] at he
  unfold PotentialKaehler.potentialMatrix
  rw [he,EllipticKernel.hermitianPartMatrix_add,EllipticKernel.hermitianPartMatrix_smul]
  rfl

lemma potentialMatrix_sub_smul {f g : V n → ℝ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) (a : ℝ) :
    PotentialKaehler.potentialMatrix (fun y => f y-a*g y) z =
      PotentialKaehler.potentialMatrix f z-(a:ℂ) • PotentialKaehler.potentialMatrix g z := by
  simpa only [neg_mul,sub_eq_add_neg,Complex.ofReal_neg,neg_smul] using potentialMatrix_affine hf hg (-a)

lemma potentialMatrix_trace_sub_smul {f g : V n → ℝ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) (a : ℝ) :
    (PotentialKaehler.potentialMatrix (fun y => f y-a*g y) z).trace.re =
      (PotentialKaehler.potentialMatrix f z).trace.re-a*(PotentialKaehler.potentialMatrix g z).trace.re := by
  rw [potentialMatrix_sub_smul hf hg,Matrix.trace_sub,Matrix.trace_smul]
  simp only [Complex.sub_re,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
end KaehlerCalculus

end
end

end OAI
