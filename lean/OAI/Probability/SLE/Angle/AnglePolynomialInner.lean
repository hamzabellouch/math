import OAI.Probability.SLE.Angle.AngleEigenOrthogonality
import OAI.Probability.SLE.Angle.AngleEigenBasis

namespace OAI

/-! The stationary weighted polynomial pairing and its finite-degree
orthogonality. This uses the actual centered generator eigenpolynomials. -/
noncomputable section
open Polynomial Set _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology

namespace SLEExactGauge

def anglePolynomialInner (κ : ℝ) (p q : ℝ[X]) : ℝ :=
  ∫ θ in (0:ℝ)..Real.pi, Real.sin θ^(4*Target.a κ)*
    anglePolynomialTest p θ*anglePolynomialTest q θ

lemma anglePolynomialInner_integrable {κ : ℝ} (hκ : 0<κ) (p q : ℝ[X]) :
    IntervalIntegrable (fun θ => Real.sin θ^(4*Target.a κ)*
      anglePolynomialTest p θ*anglePolynomialTest q θ) volume 0 Real.pi := by
  have hr : 0<4*Target.a κ := by unfold Target.a; positivity
  exact ((((Real.continuous_rpow_const hr.le).comp Real.continuous_sin).mul
    (p.continuous.comp Real.continuous_cos)).mul
    (q.continuous.comp Real.continuous_cos)).intervalIntegrable _ _

lemma anglePolynomialInner_comm (κ : ℝ) (p q : ℝ[X]) :
    anglePolynomialInner κ p q=anglePolynomialInner κ q p := by
  unfold anglePolynomialInner
  congr 1
  funext θ
  ring

lemma anglePolynomialInner_add_right {κ : ℝ} (hκ : 0<κ) (p q r : ℝ[X]) :
    anglePolynomialInner κ p (q+r)=anglePolynomialInner κ p q+anglePolynomialInner κ p r := by
  unfold anglePolynomialInner
  simp only [anglePolynomialTest,eval_add,mul_add]
  exact intervalIntegral.integral_add (anglePolynomialInner_integrable hκ p q)
    (anglePolynomialInner_integrable hκ p r)

lemma anglePolynomialInner_smul_right (κ : ℝ) (p q : ℝ[X]) (r : ℝ) :
    anglePolynomialInner κ p (r • q)=r*anglePolynomialInner κ p q := by
  unfold anglePolynomialInner
  simp only [anglePolynomialTest,eval_smul,smul_eq_mul]
  simp_rw [show ∀ θ : ℝ, Real.sin θ^(4*Target.a κ)*p.eval (Real.cos θ)*
      (r*q.eval (Real.cos θ))=r*(Real.sin θ^(4*Target.a κ)*p.eval (Real.cos θ)*
        q.eval (Real.cos θ)) by intro θ; ring]
  exact intervalIntegral.integral_const_mul _ _

def anglePolynomialInnerRight {κ : ℝ} (hκ : 0<κ) (p : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun := anglePolynomialInner κ p
  map_add' := anglePolynomialInner_add_right hκ p
  map_smul' r q := anglePolynomialInner_smul_right κ p q r

lemma anglePolynomialInner_lower_degree {κ : ℝ} (hκ : 0<κ) (n : ℕ) (q : ℝ[X])
    (hq : q.degree<n) : anglePolynomialInner κ (angleEigenPolynomial κ n) q=0 := by
  have hspan : Submodule.span ℝ ((angleEigenSequence κ) '' Iio n) ≤
      LinearMap.ker (anglePolynomialInnerRight hκ (angleEigenPolynomial κ n)) := by
    apply Submodule.span_le.mpr
    rintro p ⟨i,hi,rfl⟩
    exact angleEigenPolynomial_orthogonal hκ n i (ne_of_gt hi)
  apply hspan
  rw [(angleEigenSequence κ).span_degreeLT]
  · exact Polynomial.mem_degreeLT.mpr hq
  · intro i _hi
    change IsUnit (angleEigenPolynomial κ i).leadingCoeff
    rw [show (angleEigenPolynomial κ i).leadingCoeff=1 from angleEigenPolynomial_monic κ i]
    exact isUnit_one

lemma anglePolynomialInner_X (κ : ℝ) (p q : ℝ[X]) :
    anglePolynomialInner κ (X*p) q=anglePolynomialInner κ p (X*q) := by
  unfold anglePolynomialInner
  congr 1
  funext θ
  simp only [anglePolynomialTest,eval_mul,eval_X]
  ring

lemma anglePolynomialInner_sub_right {κ : ℝ} (hκ : 0<κ) (p q r : ℝ[X]) :
    anglePolynomialInner κ p (q-r)=anglePolynomialInner κ p q-anglePolynomialInner κ p r :=
  map_sub (anglePolynomialInnerRight hκ p) q r

lemma anglePolynomialInner_one_pos {κ : ℝ} (hκ : 0<κ) :
    0<anglePolynomialInner κ 1 1 := by
  have hr : 0<4*Target.a κ := by unfold Target.a; positivity
  simp only [anglePolynomialInner,anglePolynomialTest,eval_one,mul_one]
  apply intervalIntegral.integral_pos Real.pi_pos
    (((Real.continuous_rpow_const hr.le).comp Real.continuous_sin).continuousOn)
  · intro θ hθ
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2) _
  · refine ⟨Real.pi/2,⟨by positivity,by linarith [Real.pi_pos]⟩,?_⟩
    change 0 < Real.sin (Real.pi/2)^(4*Target.a κ)
    rw [Real.sin_pi_div_two,Real.one_rpow]
    exact zero_lt_one

end SLEExactGauge

end

end OAI
