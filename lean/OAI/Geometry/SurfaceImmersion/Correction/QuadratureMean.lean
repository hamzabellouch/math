import OAI.Geometry.Immersion.ClosedSurface.CrossModes

namespace OAI

/-! Recover the zero Fourier mode from two quadrature displacements. -/
noncomputable section
open Set Complex
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.QuadraticMean

lemma conjugate_I_smul {n : ℕ} (B : CVec n) :
    conjugate (Complex.I • B) = (-Complex.I) • conjugate B := by
  ext k
  simp [conjugate,Pi.smul_apply,smul_eq_mul]

lemma zeroPair_quadrature {n : ℕ} (θ : ℝ) (A B : CVec n) :
    2 * zeroPair A B = realMode θ A ⬝ᵥ realMode θ B +
      realMode θ (Complex.I • A) ⬝ᵥ realMode θ (Complex.I • B) := by
  have hc : (Complex.I • A) ⬝ᵥ conjugate (Complex.I • B) = A ⬝ᵥ conjugate B := by
    rw [conjugate_I_smul,smul_dotProduct,dotProduct_smul]
    simp [smul_eq_mul,← mul_assoc]
  have hd : (Complex.I • A) ⬝ᵥ (Complex.I • B) = -(A ⬝ᵥ B) := by
    rw [smul_dotProduct,dotProduct_smul]
    simp [smul_eq_mul,← mul_assoc]
  rw [realMode_self_phase,realMode_self_phase,hc,hd]
  simp only [zeroPair,mul_neg,neg_re]
  ring

lemma derivativeAmplitude_const_smul {n : ℕ} {φ : Base → ℝ} {Z : Base → CVec n}
    {p : Base} (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) (c : ℂ) (v : Base) :
    derivativeAmplitude τ φ (fun x => c • Z x) v p = c • derivativeAmplitude τ φ Z v p := by
  unfold derivativeAmplitude
  have hd : fderiv ℝ (fun x => c • Z x) p = c • fderiv ℝ Z p :=
    (hZ.hasFDerivAt.const_smul c).fderiv
  rw [hd]
  simp only [smul_apply,smul_add,smul_smul]
  congr 1
  rw [mul_comm]

end ClosedSurfaceR4.QuadraticMean
namespace ClosedSurfaceR4.RealModes
open QuadraticMean PhaseMean

lemma phaseZeroTensor_quadrature {n : ℕ} {φ : SmallModes.Base → ℝ}
    {Z : SmallModes.Base → QuadraticMean.CVec n} {p : SmallModes.Base}
    (hφ : DifferentiableAt ℝ φ p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) :
    (2 : ℝ) • phaseZeroTensor τ φ Z p =
      realMetricTensor (displacement τ φ Z) p +
      realMetricTensor (displacement τ φ (fun x => Complex.I • Z x)) p := by
  ext k
  simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,phaseZeroTensor,realMetricTensor_apply,
    realMetric,SmallModes.coordDeriv]
  have hi : DifferentiableAt ℝ (fun x => Complex.I • Z x) p := hZ.const_smul Complex.I
  rw [derivative_displacement hφ hZ,derivative_displacement hφ hZ,
    derivative_displacement hφ hi,
    derivative_displacement hφ hi,
    derivativeAmplitude_const_smul hZ,derivativeAmplitude_const_smul hZ]
  exact zeroPair_quadrature _ _ _

end ClosedSurfaceR4.RealModes

end

end OAI
