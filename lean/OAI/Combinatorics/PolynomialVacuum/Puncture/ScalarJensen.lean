import OAI.Combinatorics.PolynomialVacuum.Puncture.Reference

namespace OAI

namespace PolynomialVacuumCylinder
open Real MeasureTheory Matrix

 
theorem correctionEvaluation_integrable {n : ℕ} (u : Fin n → ℝ) :
    Integrable (fun p : ℝ=>(evenMomentEvaluation u p)^2*
      denominatorReferenceWeight p*denominatorCorrection p) := by
  apply (referenceEvaluation_integrable u).mono'
  · have hc : Continuous (evenMomentEvaluation u) := by unfold evenMomentEvaluation; fun_prop
    exact (((hc.measurable.pow_const 2).mul denominatorReferenceWeight_measurable).mul
      denominatorCorrection_continuous.measurable).aestronglyMeasurable
  · filter_upwards [] with p
    have hw : 0≤(evenMomentEvaluation u p)^2*denominatorReferenceWeight p :=
      mul_nonneg (sq_nonneg _) (denominatorReferenceWeight_pos p).le
    rw [Real.norm_of_nonneg (mul_nonneg hw (denominatorCorrection_pos p).le)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (denominatorCorrection_le_one p) hw

 

theorem denominator_scalar_jensen {n : ℕ} (u : Fin n → ℝ) (hu : u≠0) :
    (∫ p : ℝ,(evenMomentEvaluation u p)^2*denominatorReferenceWeight p*denominatorCorrection p) /
      (∫ p : ℝ,(evenMomentEvaluation u p)^2*denominatorReferenceWeight p) ≤
    Real.log ((∫ p : ℝ,(evenMomentEvaluation u p)^2*denominatorMomentWeight p) /
      (∫ p : ℝ,(evenMomentEvaluation u p)^2*denominatorReferenceWeight p)) := by
  let A := ∫ p : ℝ,(evenMomentEvaluation u p)^2*denominatorReferenceWeight p
  let B := ∫ p : ℝ,(evenMomentEvaluation u p)^2*denominatorMomentWeight p
  let C := ∫ p : ℝ,(evenMomentEvaluation u p)^2*denominatorReferenceWeight p*denominatorCorrection p
  have hA : 0<A := by
    dsimp [A]
    rw [←denominator_reference_gram_identity]
    exact (denominatorReferenceMatrix_posDef n).dotProduct_mulVec_pos hu
  have hB : 0<B := by
    dsimp [B]
    rw [←denominator_gram_identity]
    exact denominator_gram_pos u hu
  let r := B/A
  have hr : 0<r := div_pos hB hA
  have hi := integral_mono
    ((correctionEvaluation_integrable u).sub ((referenceEvaluation_integrable u).const_mul (Real.log r)))
    (((evenMomentEvaluation_integrable u).const_mul (1/r)).sub (referenceEvaluation_integrable u))
    (fun p=>show
      (evenMomentEvaluation u p)^2*denominatorReferenceWeight p*denominatorCorrection p-
        Real.log r*((evenMomentEvaluation u p)^2*denominatorReferenceWeight p) ≤
      (1/r)*((evenMomentEvaluation u p)^2*denominatorMomentWeight p)-
        (evenMomentEvaluation u p)^2*denominatorReferenceWeight p from by
      have he := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos (denominatorCorrection p)) hr)
      rw [Real.log_div (Real.exp_pos _).ne' hr.ne',Real.log_exp] at he
      have hw : 0≤(evenMomentEvaluation u p)^2*denominatorReferenceWeight p :=
        mul_nonneg (sq_nonneg _) (denominatorReferenceWeight_pos p).le
      have h := mul_le_mul_of_nonneg_left he hw
      rw [denominatorMomentWeight_factor]
      calc
        _ = ((evenMomentEvaluation u p)^2*denominatorReferenceWeight p) *
          (denominatorCorrection p-Real.log r) := by ring
        _ ≤ ((evenMomentEvaluation u p)^2*denominatorReferenceWeight p) *
          (Real.exp (denominatorCorrection p)/r-1) := h
        _ = _ := by ring)
  have hs1 := integral_sub (correctionEvaluation_integrable u)
    ((referenceEvaluation_integrable u).const_mul (Real.log r))
  have hs2 := integral_sub ((evenMomentEvaluation_integrable u).const_mul (1/r))
    (referenceEvaluation_integrable u)
  simp only [Pi.sub_apply] at hi
  rw [hs1,hs2,integral_const_mul,integral_const_mul] at hi
  change C-Real.log r*A≤(1/r)*B-A at hi
  have hz : (1/r)*B-A=0 := by dsimp [r]; field_simp [hA.ne',hB.ne']; ring
  rw [hz] at hi
  change C/A≤Real.log r
  apply (div_le_iff₀ hA).mpr
  linarith

end PolynomialVacuumCylinder

end OAI
