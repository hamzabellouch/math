import OAI.Combinatorics.PolynomialVacuum.Puncture.Gram
import OAI.Combinatorics.PolynomialVacuum.Puncture.TraceObligations

namespace OAI

namespace PolynomialVacuumCylinder
open Real MeasureTheory Matrix

theorem denominatorReferenceWeight_le (p : ℝ) :
    denominatorReferenceWeight p≤denominatorMomentWeight p := by
  rw [denominatorMomentWeight_factor]
  have he : 1≤Real.exp (denominatorCorrection p) :=
    Real.one_le_exp_iff.mpr (denominatorCorrection_pos p).le
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (denominatorReferenceWeight_pos p).le

theorem denominatorReferenceWeight_measurable : Measurable denominatorReferenceWeight := by
  unfold denominatorReferenceWeight
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

theorem denominator_reference_moment_integrable (m : ℕ) :
    Integrable (fun p : ℝ=>p^(2*m)*denominatorReferenceWeight p) := by
  apply (denominator_even_moment_integrable m).mono'
  · exact ((measurable_id.pow_const _).mul denominatorReferenceWeight_measurable).aestronglyMeasurable
  · filter_upwards [] with p
    have hp : 0≤p^(2*m) := by rw [pow_mul]; positivity
    rw [Real.norm_of_nonneg (mul_nonneg hp (denominatorReferenceWeight_pos p).le)]
    exact mul_le_mul_of_nonneg_left (denominatorReferenceWeight_le p) hp

theorem denominatorReferenceMatrix_entry_integrable (n : ℕ) (j k : Fin n) :
    Integrable (fun p : ℝ=>p^(2*j.val+2*k.val)*denominatorReferenceWeight p) := by
  rw [show 2*j.val+2*k.val=2*(j.val+k.val) by omega]
  exact denominator_reference_moment_integrable _

theorem denominatorCorrection_le_one (p : ℝ) : denominatorCorrection p≤1 := by
  apply (denominatorCorrection_decay p).trans
  apply Real.exp_le_one_iff.mpr
  have : 0≤(Real.pi/4)*|p| := by positivity
  linarith

theorem denominatorCorrectionMatrix_entry_integrable (n : ℕ) (j k : Fin n) :
    Integrable (fun p : ℝ=>p^(2*j.val+2*k.val)*
      denominatorReferenceWeight p*denominatorCorrection p) := by
  apply (denominatorReferenceMatrix_entry_integrable n j k).mono'
  · exact (((measurable_id.pow_const _).mul denominatorReferenceWeight_measurable).mul
      denominatorCorrection_continuous.measurable).aestronglyMeasurable
  · filter_upwards [] with p
    have hp : 0≤p^(2*j.val+2*k.val) := by
      rw [show 2*j.val+2*k.val=2*(j.val+k.val) by omega,pow_mul]
      positivity
    have hw : 0≤p^(2*j.val+2*k.val)*denominatorReferenceWeight p :=
      mul_nonneg hp (denominatorReferenceWeight_pos p).le
    rw [Real.norm_of_nonneg (mul_nonneg hw (denominatorCorrection_pos p).le)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (denominatorCorrection_le_one p) hw

private theorem referenceEvaluation_expand {n : ℕ} (u : Fin n → ℝ) (p : ℝ) :
    (evenMomentEvaluation u p)^2*denominatorReferenceWeight p =
      ∑ j,∑ k,(u j*u k)*(p^(2*j.val+2*k.val)*denominatorReferenceWeight p) := by
  unfold evenMomentEvaluation
  rw [pow_two,Finset.sum_mul]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

theorem referenceEvaluation_integrable {n : ℕ} (u : Fin n → ℝ) :
    Integrable (fun p : ℝ=>(evenMomentEvaluation u p)^2*denominatorReferenceWeight p) := by
  have h := integrable_finsetSum Finset.univ (fun j _=>
    integrable_finsetSum Finset.univ (fun k _=>
      (denominatorReferenceMatrix_entry_integrable n j k).const_mul (u j*u k)))
  simpa only [←referenceEvaluation_expand] using h

theorem denominator_reference_gram_identity {n : ℕ} (u : Fin n → ℝ) :
    star u ⬝ᵥ ((denominatorReferenceMatrix n)*ᵥ u) =
      ∫ p : ℝ,(evenMomentEvaluation u p)^2*denominatorReferenceWeight p := by
  simp_rw [referenceEvaluation_expand]
  rw [integral_finsetSum _ (fun j _=>integrable_finsetSum _ (fun k _=>
    (denominatorReferenceMatrix_entry_integrable n j k).const_mul (u j*u k)))]
  simp_rw [integral_finsetSum _ (fun k _=>
    (denominatorReferenceMatrix_entry_integrable n _ k).const_mul (_*u k)),integral_const_mul]
  simp only [dotProduct,mulVec,Pi.star_apply,star_trivial,denominatorReferenceMatrix]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem denominatorReferenceMatrix_posDef (n : ℕ) : (denominatorReferenceMatrix n).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext j k
    simp only [conjTranspose_apply,star_trivial,denominatorReferenceMatrix]
    apply integral_congr_ae
    filter_upwards [] with p
    rw [Nat.add_comm]
  · intro u hu
    rw [denominator_reference_gram_identity]
    have ha := denominator_gram_pos u hu
    rw [denominator_gram_identity] at ha
    have hi := integral_mono (evenMomentEvaluation_integrable u)
      ((referenceEvaluation_integrable u).const_mul (3/2))
      (fun p=>show (evenMomentEvaluation u p)^2*denominatorMomentWeight p≤
        (3/2)*((evenMomentEvaluation u p)^2*denominatorReferenceWeight p) from
          (mul_le_mul_of_nonneg_left (denominatorMomentWeight_le_reference p) (sq_nonneg _)).trans_eq (by ring))
    rw [integral_const_mul] at hi
    linarith

theorem denominatorReferenceMatrix_det_pos (n : ℕ) : 0<(denominatorReferenceMatrix n).det :=
  (denominatorReferenceMatrix_posDef n).det_pos

end PolynomialVacuumCylinder

end OAI
