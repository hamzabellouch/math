import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralWitnessed
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralSmallEnergy
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFirstBinSum
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLaterBinSum

namespace OAI

/-! Literal logarithmic prime polynomials and their small/large frequency
sets. These sets supply the hypotheses of the general cofactor estimates. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped Classical

noncomputable def mrtLogPrimePolynomial (S : Finset ℕ) (F : ℕ → ℂ)
    (H : ℝ) (k : ℕ) : ℝ → ℂ :=
  mrtExponentialPolynomial (S.filter (fun p => mrtPrimeLogBin H p = k))
    (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ))

noncomputable def mrtLogSmallSet (S : Finset ℕ) (F : ℕ → ℂ)
    (H : ℝ) (K : Finset ℕ) (a : ℝ) : Set ℝ :=
  {t | ∀ k ∈ K, ‖mrtLogPrimePolynomial S F H k t‖ ≤
    Real.exp (-a*Real.log (mrtPrimeLogLower H k))}

noncomputable def mrtLogLargeSet (S : Finset ℕ) (F : ℕ → ℂ)
    (H : ℝ) (K : Finset ℕ) (a : ℝ) : Set ℝ :=
  {t | ∃ k ∈ K, Real.exp (-a*Real.log (mrtPrimeLogLower H k)) <
    ‖mrtLogPrimePolynomial S F H k t‖}

lemma mrt_log_prime_polynomial_continuous (S : Finset ℕ) (F : ℕ → ℂ)
    (H : ℝ) (k : ℕ) : Continuous (mrtLogPrimePolynomial S F H k) :=
  mrtExponentialPolynomial_continuous _ _ _

lemma mrt_log_small_set_measurable (S : Finset ℕ) (F : ℕ → ℂ)
    (H : ℝ) (K : Finset ℕ) (a : ℝ) :
    MeasurableSet (mrtLogSmallSet S F H K a) := by
  have he : mrtLogSmallSet S F H K a = ⋂ k ∈ K,
      {t | ‖mrtLogPrimePolynomial S F H k t‖ ≤
        Real.exp (-a*Real.log (mrtPrimeLogLower H k))} := by
    ext t
    simp [mrtLogSmallSet]
  rw [he]
  exact K.measurableSet_biInter (fun k _ =>
    (isClosed_le (mrt_log_prime_polynomial_continuous S F H k).norm continuous_const).measurableSet)

lemma mrt_log_large_set_measurable (S : Finset ℕ) (F : ℕ → ℂ)
    (H : ℝ) (K : Finset ℕ) (a : ℝ) :
    MeasurableSet (mrtLogLargeSet S F H K a) := by
  have he : mrtLogLargeSet S F H K a = ⋃ k ∈ K,
      {t | Real.exp (-a*Real.log (mrtPrimeLogLower H k)) <
        ‖mrtLogPrimePolynomial S F H k t‖} := by
    ext t
    simp [mrtLogLargeSet]
  rw [he]
  exact K.measurableSet_biUnion (fun k _ =>
    (isOpen_lt continuous_const (mrt_log_prime_polynomial_continuous S F H k).norm).measurableSet)

lemma mrt_log_bin_lower_gt_one {H P Q : ℝ} (hH : 2 ≤ H)
    (hP : 0 < P) (hlogP : 2 ≤ Real.log P) {k : ℕ}
    (hk : k ∈ mrtLogBins H P Q) : 1 < mrtPrimeLogLower H k := by
  have hl := mrt_log_bin_lower_endpoint (by linarith : 1 ≤ H) hP (mem_Icc.mp hk).1
  have he : Real.exp 1 ≤ Real.exp (-1)*P := by
    rw [show Real.exp (-1)*P = Real.exp (Real.log P-1) by
      rw [Real.exp_sub, Real.exp_neg, Real.exp_log hP]; ring]
    exact Real.exp_le_exp.mpr (by linarith)
  exact (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)).trans_le (he.trans hl)

lemma mrt_log_bin_prime_data (S : Finset ℕ) {H P Q : ℝ} (hH : 2 ≤ H)
    (hP : 0 < P) (hprime : ∀ p ∈ S, p.Prime)
    (hrange : ∀ p ∈ S, P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Q) :
    (∀ p ∈ S, mrtPrimeLogBin H p ∈ mrtLogBins H P Q) ∧
    (∀ p ∈ S, mrtPrimeLogLower H (mrtPrimeLogBin H p) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (1/H)*mrtPrimeLogLower H (mrtPrimeLogBin H p)) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    exact mrt_prime_log_bin_range (by linarith) hP (hrange p hp).1 (hrange p hp).2
  · intro p hp
    exact mrt_prime_log_bin_bounds (by linarith) (hprime p hp).one_le

end TwoPointCorrelations

end OAI
