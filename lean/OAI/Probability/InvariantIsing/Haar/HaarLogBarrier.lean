import OAI.Probability.InvariantIsing.Haar.HaarLogCurvature
import OAI.Probability.InvariantIsing.Haar.HaarMinimumGradient

namespace OAI

/-! The pointwise minimum inequality for a logarithmic heat-gradient barrier. -/
noncomputable section
open Matrix MvPolynomial
namespace InvariantIsing

def haarLogBarrier {N : ℕ} (p : MatrixPolynomial N) (a : ℝ) : MatrixPolynomial N :=
  a • p^2-haarPolynomialGamma p p

lemma haarLogBarrier_eval {N : ℕ} (p : MatrixPolynomial N) (a : ℝ)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (haarLogBarrier p a) =
      a*(matrixPolynomialEval M p)^2-matrixPolynomialEval M (haarPolynomialGamma p p) := by
  simp only [haarLogBarrier,map_sub,map_smul,map_pow,smul_eq_mul]

lemma haarLogBarrier_laplacian {N : ℕ} (p : MatrixPolynomial N) (a : ℝ)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (haarPolynomialLaplacian N (haarLogBarrier p a)) =
      2*a*(matrixPolynomialEval M p*matrixPolynomialEval M (haarPolynomialLaplacian N p)+
        matrixPolynomialEval M (haarPolynomialGamma p p))-
        matrixPolynomialEval M (haarPolynomialLaplacian N (haarPolynomialGamma p p)) := by
  simp only [haarLogBarrier,map_sub,map_smul,haarPolynomialLaplacian_sq,
    map_mul,map_ofNat,map_add,smul_eq_mul]
  ring

lemma haarLogBarrier_gamma {N : ℕ} (p : MatrixPolynomial N) (a : ℝ)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (haarPolynomialGamma p (haarLogBarrier p a)) =
      2*a*matrixPolynomialEval M p*matrixPolynomialEval M (haarPolynomialGamma p p)-
        matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialGamma p p)) := by
  simp only [haarLogBarrier,haarPolynomialGamma_sub,haarPolynomialGamma_smul,
    haarPolynomialGamma_sq,map_sub,map_smul,map_mul,map_ofNat,smul_eq_mul]
  ring

lemma haarLogBarrier_min_derivative_lower {N : ℕ} (p : MatrixPolynomial N) (a : ℝ)
    (U : SpecialOrthogonal N) (hu : haarPolynomialValue p U ≠ 0)
    (hmin : ∀ V : SpecialOrthogonal N,
      haarPolynomialValue (haarLogBarrier p a) U ≤ haarPolynomialValue (haarLogBarrier p a) V) :
    -2*((N:ℝ)-2)*a*(haarPolynomialValue p U)^2+
        2*a*haarPolynomialValue p U*haarPolynomialValue (haarPolynomialLaplacian N p) U-
        2*haarPolynomialValue (haarPolynomialGamma p (haarPolynomialLaplacian N p)) U ≥
      (-2*((N:ℝ)-2)+2*haarPolynomialValue (haarPolynomialGamma p p) U/
        (haarPolynomialValue p U)^2)*haarPolynomialValue (haarLogBarrier p a) U := by
  let M : Matrix (Fin N) (Fin N) ℝ := U
  have hc := haarLogCurvature p M (1/matrixPolynomialEval M p)
  have hl := haarPolynomialLaplacian_nonneg_at_min (haarLogBarrier p a) U hmin
  have hg := haarPolynomialGamma_zero_at_min (haarLogBarrier p a) p U hmin
  change 0 ≤ matrixPolynomialEval M (haarPolynomialLaplacian N (haarLogBarrier p a)) at hl
  change matrixPolynomialEval M (haarPolynomialGamma p (haarLogBarrier p a)) = 0 at hg
  rw [haarLogBarrier_laplacian] at hl
  rw [haarLogBarrier_gamma] at hg
  change matrixPolynomialEval M p ≠ 0 at hu
  change -2*((N:ℝ)-2)*a*(matrixPolynomialEval M p)^2+
      2*a*matrixPolynomialEval M p*matrixPolynomialEval M (haarPolynomialLaplacian N p)-
      2*matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialLaplacian N p)) ≥ _
  rw [show haarPolynomialValue (haarLogBarrier p a) U =
    matrixPolynomialEval M (haarLogBarrier p a) from rfl,haarLogBarrier_eval]
  have hq : matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialGamma p p)) /
      matrixPolynomialEval M p = 2*a*matrixPolynomialEval M (haarPolynomialGamma p p) := by
    rw [div_eq_iff hu]
    linear_combination -hg
  rw [div_eq_mul_inv] at hq
  have hce : ((N:ℝ)-2)*matrixPolynomialEval M (haarPolynomialGamma p p) ≤
      matrixPolynomialEval M (haarPolynomialLaplacian N (haarPolynomialGamma p p))/2-
      matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialLaplacian N p))-
      2*a*matrixPolynomialEval M (haarPolynomialGamma p p)+
      (matrixPolynomialEval M (haarPolynomialGamma p p))^2/(matrixPolynomialEval M p)^2 := by
    convert hc using 1
    simp only [one_div]
    rw [mul_comm ((matrixPolynomialEval M p)⁻¹),hq]
    ring
  have hid :
      (-2*((N:ℝ)-2)+2*matrixPolynomialEval M (haarPolynomialGamma p p)/(matrixPolynomialEval M p)^2)*
          (a*(matrixPolynomialEval M p)^2-matrixPolynomialEval M (haarPolynomialGamma p p)) =
      -2*((N:ℝ)-2)*a*(matrixPolynomialEval M p)^2+
        2*((N:ℝ)-2)*matrixPolynomialEval M (haarPolynomialGamma p p)+
        2*a*matrixPolynomialEval M (haarPolynomialGamma p p)-
        2*(matrixPolynomialEval M (haarPolynomialGamma p p))^2/(matrixPolynomialEval M p)^2 := by
    field_simp
    ring
  change _ ≥ (-2*((N:ℝ)-2)+2*matrixPolynomialEval M (haarPolynomialGamma p p)/
    (matrixPolynomialEval M p)^2)*(a*(matrixPolynomialEval M p)^2-
      matrixPolynomialEval M (haarPolynomialGamma p p))
  rw [hid]
  linear_combination hl+2*hce

end InvariantIsing

end

end OAI
