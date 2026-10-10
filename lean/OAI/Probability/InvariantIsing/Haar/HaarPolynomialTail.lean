import OAI.Probability.InvariantIsing.Haar.HaarPolynomialMomentShift

namespace OAI

/-! Chernoff bounds for centered polynomial observables of the Haar matrix. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Set
namespace InvariantIsing

theorem haarPolynomial_chernoff {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : MatrixPolynomial N) (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ U : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) U ≤ C)
    (r β : ℝ) (hβ : 0 < β) :
    μ.real {U | r ≤ haarPolynomialValue p U-(∫ V, haarPolynomialValue p V ∂μ)} ≤
      Real.exp (C/(2*((N:ℝ)-2))*β^2-β*r) := by
  let m := ∫ V, haarPolynomialValue p V ∂μ
  let A := C/(2*((N:ℝ)-2))
  let F (U : SpecialOrthogonal N) := Real.exp (β*(haarPolynomialValue p U-m))
  have hfi : Integrable F μ := continuous_haar_integrable μ _
    (Real.continuous_exp.comp (continuous_const.mul ((continuous_haarPolynomialValue p).sub continuous_const)))
  have hmoment : haarPolynomialMoment μ p β ≤ Real.exp (m*β+A*β^2) := by
    have hh := Real.exp_le_exp.mpr (haarPolynomialMoment_log_bound hN μ p C hC hG hβ)
    rwa [Real.exp_log (haarPolynomialMoment_pos μ p β)] at hh
  have hI : (∫ U, F U ∂μ) ≤ Real.exp (A*β^2) := by
    have he : (∫ U, F U ∂μ) = Real.exp (-β*m)*haarPolynomialMoment μ p β := by
      rw [haarPolynomialMoment,← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all μ fun U => by
        change Real.exp (β*(haarPolynomialValue p U-m)) =
          Real.exp (-β*m)*Real.exp (β*haarPolynomialValue p U)
        rw [← Real.exp_add]
        congr 1
        ring
    rw [he]
    calc
      _ ≤ Real.exp (-β*m)*Real.exp (m*β+A*β^2) :=
        mul_le_mul_of_nonneg_left hmoment (Real.exp_pos _).le
      _ = Real.exp (A*β^2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hset : {U | Real.exp (β*r) ≤ F U} =
      {U | r ≤ haarPolynomialValue p U-m} := by
    ext U
    simp only [mem_ofPred_eq,F,Real.exp_le_exp]
    exact mul_le_mul_iff_right₀ hβ
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ fun U => (Real.exp_pos _).le)
    hfi (Real.exp (β*r))
  rw [hset] at hm
  have hb : μ.real {U | r ≤ haarPolynomialValue p U-m} ≤ Real.exp (A*β^2)/Real.exp (β*r) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith [hm]
  simpa only [Real.exp_sub] using hb

end InvariantIsing

end

end OAI
