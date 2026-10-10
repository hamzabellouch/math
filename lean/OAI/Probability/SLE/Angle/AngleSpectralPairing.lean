import OAI.Probability.SLE.Angle.AngleStationaryPairing
import OAI.Probability.SLE.Angle.AngleSpectralBounds

namespace OAI

/-! Exact stationary moments of the normalized polynomial kernel terms. -/
noncomputable section
open Polynomial Set _root_.MeasureTheory _root_.OAI.MeasureTheory

namespace SLEExactGauge

lemma anglePolynomialTest_bound (p : ℝ[X]) :
    ∃ M : ℝ, ∀ θ : ℝ, ‖anglePolynomialTest p θ‖≤M := by
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1)).exists_bound_of_continuousOn
    p.continuous.continuousOn
  exact ⟨M,fun θ => hM (Real.cos θ) ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩⟩

lemma anglePolynomialTest_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (p : ℝ[X]) :
    Integrable (anglePolynomialTest p) μ := by
  obtain ⟨M,hM⟩ := anglePolynomialTest_bound p
  exact Integrable.of_bound (p.continuous.comp Real.continuous_cos).aestronglyMeasurable M
    (Filter.Eventually.of_forall hM)

lemma anglePolynomialTest_mul_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (p q : ℝ[X]) :
    Integrable (fun θ => anglePolynomialTest p θ*anglePolynomialTest q θ) μ := by
  have he := anglePolynomialTest_integrable μ (p*q)
  change Integrable (fun θ => (p*q).eval (Real.cos θ)) μ at he
  simpa only [anglePolynomialTest,eval_mul] using he

lemma angleSpectralFactor_pairing {κ : ℝ} (hκ : 0<κ) (n m : ℕ) (x : ℝ) :
    (∫ φ, angleSpectralFactor κ n x (Real.cos φ)*
      anglePolynomialTest (angleEigenPolynomial κ m) φ ∂Target.angleLaw κ)=
        if n=m then (angleEigenPolynomial κ m).eval x else 0 := by
  have he : (fun φ => angleSpectralFactor κ n x (Real.cos φ)*
      anglePolynomialTest (angleEigenPolynomial κ m) φ)=
      fun φ => (angleEigenSquareNorm κ 0/angleEigenSquareNorm κ n*
        (angleEigenPolynomial κ n).eval x)*
      (anglePolynomialTest (angleEigenPolynomial κ n) φ*
        anglePolynomialTest (angleEigenPolynomial κ m) φ) := by
    funext φ
    unfold angleSpectralFactor anglePolynomialTest
    ring
  rw [he,integral_const_mul,angleLaw_polynomial_pairing hκ]
  by_cases hnm : n=m
  · subst m
    rw [ite_eq_left rfl]
    change (angleEigenSquareNorm κ 0/angleEigenSquareNorm κ n*
        (angleEigenPolynomial κ n).eval x)*
      ((angleEigenSquareNorm κ 0)⁻¹*angleEigenSquareNorm κ n)=_
    field_simp [(angleEigenSquareNorm_pos hκ n).ne',
      (angleEigenSquareNorm_zero_pos hκ).ne']
  · rw [ite_eq_right hnm]
    have hz : anglePolynomialInner κ (angleEigenPolynomial κ n) (angleEigenPolynomial κ m)=0 :=
      angleEigenPolynomial_orthogonal hκ n m hnm
    rw [hz,mul_zero,mul_zero]

lemma angleLaw_eigen_mean {κ : ℝ} (hκ : 0<κ) (n : ℕ) :
    (∫ φ, anglePolynomialTest (angleEigenPolynomial κ n) φ ∂Target.angleLaw κ)=
      if n=0 then 1 else 0 := by
  have he := angleLaw_polynomial_pairing hκ (angleEigenPolynomial κ n) (angleEigenPolynomial κ 0)
  simp only [angleEigenPolynomial_zero,anglePolynomialTest,eval_one,mul_one] at he
  change (∫ φ, (angleEigenPolynomial κ n).eval (Real.cos φ) ∂Target.angleLaw κ)=_
  rw [he]
  by_cases hn : n=0
  · subst n
    rw [ite_eq_left rfl]
    rw [← angleEigenPolynomial_zero κ]
    change (angleEigenSquareNorm κ 0)⁻¹*angleEigenSquareNorm κ 0=1
    exact inv_mul_cancel₀ (angleEigenSquareNorm_zero_pos hκ).ne'
  · rw [ite_eq_right hn]
    have hz : anglePolynomialInner κ (angleEigenPolynomial κ n) 1=0 := by
      rw [← angleEigenPolynomial_zero κ]
      exact angleEigenPolynomial_orthogonal hκ n 0 hn
    rw [hz,mul_zero]

end SLEExactGauge

end

end OAI
