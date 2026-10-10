import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogPartition
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtractionErrors

namespace OAI

/-! Uniform bounds for the actual first-small logarithmic classes.
The first-band cost occurs once; the later costs form an inverse-square sum. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped Classical

noncomputable def mrtLogExtractionError (V : ℕ → Finset ℕ)
    (P Q η : ℝ) (j : ℕ) : ℝ :=
  (∑ p ∈ V j, 1/(p:ℝ)^2) + (∑ p ∈ V j, 1/(p:ℝ)^2)^2 +
    2/mrtResolution P Q η j

theorem mrt_log_class_energy (V : ℕ → Finset ℕ) (J : ℕ)
    (hprime : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j, p.Prime)
    (hdis : Set.PairwiseDisjoint (Finset.Icc 1 J : Set ℕ) V)
    {P Q η : ℝ} (hP0 : 0 < P) (hQ0 : 0 < Q)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q) (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j)
    {N : ℕ} (hN : 0 < N) (hsize : 2*Q ≤ (N:ℝ))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) {r : ℕ} (hr : r ∈ range J) :
    (∫ t in mrtFirstLogClass V F P Q η r T,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
      2816*Real.exp 1*(T/N+1)*mrtLogExtractionError V P Q η (r+1) +
      (if r = 0 then
        1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹ else 0) +
      (T/N+1)*P⁻¹*(((r:ℝ)+1)^2)⁻¹ := by
  have hp1 : 1 ≤ P := by
    rw [← Real.exp_log hP0]
    exact Real.one_le_exp (by linarith)
  have hlast : r+1 ∈ Finset.Icc 1 J := mem_Icc.mpr ⟨by omega, by have := mem_range.mp hr; omega⟩
  have hnon : 0 ≤ (T/N+1)*P⁻¹*(((r:ℝ)+1)^2)⁻¹ := by positivity
  by_cases hzero : r = 0
  · subst r
    have hrange1 : ∀ p ∈ V 1, P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Q := by
      simpa only [mrtBandLower_one P Q hP0, mrtBandUpper_one Q hQ0] using hrange 1 hlast
    have hb := mrt_first_log_class_energy (Finset.Icc 1 J) V hprime hdis hlast hp1 hQ0 hQ
      hη.le hη' hH hrange1 hN hsize F hF hFb hT
    rw [mrt_first_log_class_zero V F hP0 hQ0]
    simp only [Nat.zero_add, ite_true, mrtLogExtractionError, mrtResolution_one]
    exact hb.trans (le_add_of_nonneg_right hnon)
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hprev : j+1 ∈ Finset.Icc 1 J := mem_Icc.mpr ⟨by omega, by have := mem_range.mp hr; omega⟩
    have hb := mrt_later_log_class_energy (Finset.Icc 1 J) V hprime hdis hlast
      (V (j+1)) (hprime (j+1) hprev) hP0 hP hQ hPQ hη (by linarith) hbudget hH j
      (hrange (j+1) hprev) (hrange (j+2) hlast) hN F hF hFb hT
    have hi : (∫ t in mrtFirstLogClass V F P Q η (j+1) T,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
        ∫ t in mrtLaterLogClass (V (j+1)) (V (j+2)) F P Q η j T,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2 :=
      setIntegral_mono_set
        (mrt_continuous_square_integrable (mrtExponentialPolynomial_continuous _ _ _)
          hT.le inter_subset_left)
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (Filter.Eventually.of_forall (mrt_first_log_class_succ_subset V F P Q η j T))
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_one_ne_zero,
      ite_false, add_zero, mrtLogExtractionError, Nat.cast_add, Nat.cast_one,
      add_assoc, show (1:ℕ)+1 = 2 by decide,
      show (1:ℝ)+1 = 2 by norm_num] using hi.trans hb

end TwoPointCorrelations

end OAI
