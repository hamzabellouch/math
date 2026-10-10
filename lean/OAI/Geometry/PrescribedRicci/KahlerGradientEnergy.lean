import Mathlib
import OAI.Geometry.PrescribedRicci.LocalKahlerEnergy

namespace OAI

/-! Kahler Gradient Energy. -/

noncomputable section
open Matrix Filter Set Topology MeasureTheory
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise Classical
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ}

lemma barDeriv_congr {f h : Coordinates d → ℂ} {z : Coordinates d}
    (he : f =ᶠ[𝓝 z] h) (i : Fin d) : barDeriv f z i = barDeriv h z i := by
  unfold barDeriv
  rw [he.fderiv_eq]

lemma barDeriv_add {f h : Coordinates d → ℂ} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin d) :
    barDeriv (fun y => f y + h y) z i = barDeriv f z i + barDeriv h z i := by
  unfold barDeriv
  rw [fderiv_fun_add hf hh]
  simp only [_root_.add_apply]
  ring

lemma barDeriv_ofReal {φ : Coordinates d → ℝ} {z : Coordinates d}
    (hφ : DifferentiableAt ℝ φ z) (i : Fin d) :
    barDeriv (fun y => (φ y : ℂ)) z i = star (holRealDeriv φ z i) := by
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp z hφ.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (φ y : ℂ)) z = _ at hd
  unfold barDeriv holRealDeriv holRealForm
  rw [hd]
  apply Complex.ext <;> simp

lemma holRealDeriv_mul {φ ψ : Coordinates d → ℝ} {z : Coordinates d}
    (hφ : DifferentiableAt ℝ φ z) (hψ : DifferentiableAt ℝ ψ z) (j : Fin d) :
    holRealDeriv (fun y => φ y * ψ y) z j =
      (φ z : ℂ) * holRealDeriv ψ z j + (ψ z : ℂ) * holRealDeriv φ z j := by
  unfold holRealDeriv
  rw [fderiv_fun_mul hφ hψ, map_add, map_smul, map_smul]
  simp only [Complex.real_smul]

lemma potentialMatrix_mul {φ ψ : Coordinates d → ℝ} {z : Coordinates d}
    (hφ : ContDiffAt ℝ ∞ φ z) (hψ : ContDiffAt ℝ ∞ ψ z) (i j : Fin d) :
    PotentialKaehler.potentialMatrix (fun y => φ y * ψ y) z i j =
      (φ z : ℂ) * PotentialKaehler.potentialMatrix ψ z i j +
      (ψ z : ℂ) * PotentialKaehler.potentialMatrix φ z i j +
      star (holRealDeriv φ z i) * holRealDeriv ψ z j +
      star (holRealDeriv ψ z i) * holRealDeriv φ z j := by
  rw [← barDeriv_holRealDeriv (hφ.mul hψ)]
  have hev : (fun y => holRealDeriv (fun w => φ w * ψ w) y j) =ᶠ[𝓝 z]
      fun y => (φ y : ℂ) * holRealDeriv ψ y j + (ψ y : ℂ) * holRealDeriv φ y j := by
    filter_upwards [(hφ.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp),
      (hψ.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)] with y hyφ hyψ
    exact holRealDeriv_mul (hyφ.differentiableAt (by simp)) (hyψ.differentiableAt (by simp)) j
  rw [barDeriv_congr hev]
  have hdφ := hφ.differentiableAt (by simp)
  have hdψ := hψ.differentiableAt (by simp)
  have hcφ : DifferentiableAt ℝ (fun y => (φ y : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hdφ
  have hcψ : DifferentiableAt ℝ (fun y => (ψ y : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hdψ
  have hhφ := (contDiffAt_holRealDeriv hφ j).differentiableAt (by simp)
  have hhψ := (contDiffAt_holRealDeriv hψ j).differentiableAt (by simp)
  rw [barDeriv_add (hcφ.fun_mul hhψ) (hcψ.fun_mul hhφ),
    barDeriv_mul hcφ hhψ, barDeriv_mul hcψ hhφ,
    barDeriv_ofReal hdφ, barDeriv_ofReal hdψ,
    barDeriv_holRealDeriv hψ, barDeriv_holRealDeriv hφ]
  ring

def gradientPair (H : Matrix (Fin d) (Fin d) ℂ) (p q : Fin d → ℂ) : ℂ :=
  ∑ j, ∑ i, H⁻¹ j i * star (p i) * q j

lemma gradientPair_star (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (p q : Fin d → ℂ) : star (gradientPair H p q) = gradientPair H q p := by
  have hi := hH.inv
  unfold gradientPair
  simp only [star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have he : star (H⁻¹ i j) = H⁻¹ j i := congrFun (congrFun hi.eq j) i
  rw [he]
  ring

lemma gradientPair_self_nonneg (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.PosDef)
    (p : Fin d → ℂ) : 0 ≤ (gradientPair H p p).re := by
  have hp := hH.inv.posSemidef.dotProduct_mulVec_nonneg (star p)
  have he : gradientPair H p p = star (star p) ⬝ᵥ (H⁻¹ *ᵥ star p) := by
    simp only [gradientPair, dotProduct, Matrix.mulVec, Pi.star_apply, star_star, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  exact (Complex.nonneg_iff.mp hp).1

lemma trace_hessian_product {φ ψ : Coordinates d → ℝ} {z : Coordinates d}
    (hφ : ContDiffAt ℝ ∞ φ z) (hψ : ContDiffAt ℝ ∞ ψ z)
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    ((H⁻¹ * PotentialKaehler.potentialMatrix (fun y => φ y * ψ y) z).trace).re =
      φ z * ((H⁻¹ * PotentialKaehler.potentialMatrix ψ z).trace).re +
      ψ z * ((H⁻¹ * PotentialKaehler.potentialMatrix φ z).trace).re +
      2 * (gradientPair H (holRealDeriv φ z) (holRealDeriv ψ z)).re := by
  have he : (H⁻¹ * PotentialKaehler.potentialMatrix (fun y => φ y * ψ y) z).trace =
      (φ z : ℂ) * (H⁻¹ * PotentialKaehler.potentialMatrix ψ z).trace +
      (ψ z : ℂ) * (H⁻¹ * PotentialKaehler.potentialMatrix φ z).trace +
      gradientPair H (holRealDeriv φ z) (holRealDeriv ψ z) +
      gradientPair H (holRealDeriv ψ z) (holRealDeriv φ z) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, potentialMatrix_mul hφ hψ,
      gradientPair, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [he, ← gradientPair_star H hH]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.star_def, Complex.conj_re]
  ring

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI
