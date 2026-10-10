import OAI.Probability.SLE.Angle.AngleStationaryFlux

namespace OAI

/-! Symmetry under the paper's stationary angular weight, and orthogonality
of the actual centered-generator polynomial eigenfunctions. -/
noncomputable section
open Polynomial Set _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology

namespace SLEExactGauge

lemma anglePolynomialWronskian_hasDerivAt {κ : ℝ} (hκ : 0<κ) (p q : ℝ[X]) {θ : ℝ}
    (hθ : θ∈Icc (0:ℝ) Real.pi) :
    HasDerivAt (fun θ => anglePolynomialTest q θ*anglePolynomialFlux κ p θ -
      anglePolynomialTest p θ*anglePolynomialFlux κ q θ)
      (Real.sin θ^(4*Target.a κ)*
        (anglePolynomialTest q θ*(anglePolynomialGenerator κ p).eval (Real.cos θ) -
          anglePolynomialTest p θ*(anglePolynomialGenerator κ q).eval (Real.cos θ))) θ := by
  have hp := (anglePolynomialTest_hasDerivAt q θ).mul (anglePolynomialFlux_hasDerivAt hκ p hθ)
  have hq := (anglePolynomialTest_hasDerivAt p θ).mul (anglePolynomialFlux_hasDerivAt hκ q hθ)
  apply (hp.sub hq).congr_deriv
  simp only [anglePolynomialTest,anglePolynomialFlux]
  ring

lemma anglePolynomialGenerator_symmetric {κ : ℝ} (hκ : 0<κ) (p q : ℝ[X]) :
    (∫ θ in (0:ℝ)..Real.pi, Real.sin θ^(4*Target.a κ)*
      anglePolynomialTest q θ*(anglePolynomialGenerator κ p).eval (Real.cos θ)) =
    ∫ θ in (0:ℝ)..Real.pi, Real.sin θ^(4*Target.a κ)*
      anglePolynomialTest p θ*(anglePolynomialGenerator κ q).eval (Real.cos θ) := by
  have hr : 0<4*Target.a κ := by unfold Target.a; positivity
  have hc (p q : ℝ[X]) : Continuous (fun θ => Real.sin θ^(4*Target.a κ)*
      anglePolynomialTest q θ*(anglePolynomialGenerator κ p).eval (Real.cos θ)) :=
    (((Real.continuous_rpow_const hr.le).comp Real.continuous_sin).mul
      (q.continuous.comp Real.continuous_cos)).mul
      ((anglePolynomialGenerator κ p).continuous.comp Real.continuous_cos)
  have hi : IntervalIntegrable (fun θ => Real.sin θ^(4*Target.a κ)*
      (anglePolynomialTest q θ*(anglePolynomialGenerator κ p).eval (Real.cos θ) -
        anglePolynomialTest p θ*(anglePolynomialGenerator κ q).eval (Real.cos θ)))
      volume 0 Real.pi := by
    convert (((hc p q).sub (hc q p)).intervalIntegrable (μ := volume) 0 Real.pi) using 1
    ext θ
    simp only [Pi.sub_apply]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ hθ => anglePolynomialWronskian_hasDerivAt hκ p q
      (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ))
    hi
  simp only [mul_sub,← mul_assoc] at he
  rw [intervalIntegral.integral_sub ((hc p q).intervalIntegrable _ _)
    ((hc q p).intervalIntegrable _ _)] at he
  have hzero : ∀ p : ℝ[X], anglePolynomialFlux κ p Real.pi=0 ∧ anglePolynomialFlux κ p 0=0 := by
    intro p
    simp [anglePolynomialFlux,Real.zero_rpow (by linarith : 4*Target.a κ+1≠0)]
  rw [(hzero p).1,(hzero q).1,(hzero p).2,(hzero q).2] at he
  simpa only [mul_zero,sub_self,sub_eq_zero] using he

lemma angleEigenPolynomial_orthogonal {κ : ℝ} (hκ : 0<κ) (n m : ℕ) (hnm : n≠m) :
    (∫ θ in (0:ℝ)..Real.pi, Real.sin θ^(4*Target.a κ)*
      anglePolynomialTest (angleEigenPolynomial κ n) θ*
        anglePolynomialTest (angleEigenPolynomial κ m) θ)=0 := by
  have he := anglePolynomialGenerator_symmetric hκ
    (angleEigenPolynomial κ n) (angleEigenPolynomial κ m)
  simp_rw [angleEigenPolynomial_eigen hκ,eval_mul,eval_neg,eval_C] at he
  have hn (θ : ℝ) : Real.sin θ^(4*Target.a κ)*anglePolynomialTest (angleEigenPolynomial κ m) θ*
      (-anglePolynomialEigenvalue κ n*(angleEigenPolynomial κ n).eval (Real.cos θ)) =
      -anglePolynomialEigenvalue κ n*(Real.sin θ^(4*Target.a κ)*
        anglePolynomialTest (angleEigenPolynomial κ n) θ*anglePolynomialTest (angleEigenPolynomial κ m) θ) := by
    simp only [anglePolynomialTest]
    ring
  have hm (θ : ℝ) : Real.sin θ^(4*Target.a κ)*anglePolynomialTest (angleEigenPolynomial κ n) θ*
      (-anglePolynomialEigenvalue κ m*(angleEigenPolynomial κ m).eval (Real.cos θ)) =
      -anglePolynomialEigenvalue κ m*(Real.sin θ^(4*Target.a κ)*
        anglePolynomialTest (angleEigenPolynomial κ n) θ*anglePolynomialTest (angleEigenPolynomial κ m) θ) := by
    simp only [anglePolynomialTest]
    ring
  simp_rw [hn,hm,intervalIntegral.integral_const_mul] at he
  have hd : anglePolynomialEigenvalue κ n-anglePolynomialEigenvalue κ m≠0 :=
    sub_ne_zero.mpr ((anglePolynomialEigenvalue_strictMono hκ).injective.ne hnm)
  have hz : (anglePolynomialEigenvalue κ n-anglePolynomialEigenvalue κ m)*
      (∫ θ in (0:ℝ)..Real.pi, Real.sin θ^(4*Target.a κ)*
        anglePolynomialTest (angleEigenPolynomial κ n) θ*anglePolynomialTest (angleEigenPolynomial κ m) θ)=0 := by
    linarith
  exact (mul_eq_zero.mp hz).resolve_left hd

end SLEExactGauge

end

end OAI
