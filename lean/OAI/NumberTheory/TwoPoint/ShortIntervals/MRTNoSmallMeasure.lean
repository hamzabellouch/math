import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLargeMeasure
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogPartition
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtractionErrors

namespace OAI

/-! The actual no-small frequency class is covered by large values in
any selected band, in particular the final band. All moment costs remain explicit. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtShortPrimeLargeCost (Y V T : ℝ) (r : ℕ) : ℝ :=
  (8*Real.exp 1*(T+((2*⌈Y⌉₊)^r:ℕ))*(r.factorial:ℝ)*(2/Y)^r)/V^(2*r)

theorem mrt_short_prime_large_measure (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) {Y V T : ℝ} (hY : 1 < Y)
    (hbin : ∀ p ∈ S, Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y)
    (F : ℕ → ℂ) (hF : OneBounded F) (r : ℕ) (hT : 0 < T) (hV : 0 < V)
    {E : Set ℝ} (hE : MeasurableSet E) (hET : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖mrtExponentialPolynomial S
      (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖) :
    (∫ _t in E, (1:ℝ)) ≤ mrtShortPrimeLargeCost Y V T r := by
  have hcap (p : ℕ) (hp : p ∈ S) : p ≤ 2*⌈Y⌉₊ := by
    have hh := (hbin p hp).2.trans
      (mul_le_mul_of_nonneg_left (Nat.le_ceil Y) (by norm_num : (0:ℝ) ≤ 2))
    exact_mod_cast hh
  have hmass : (∑ p ∈ S, ‖F p/(p:ℂ)‖^2) ≤ 2/Y := by
    calc
      _ ≤ ∑ p ∈ S, 1/(p:ℝ)^2 := by
        apply sum_le_sum
        intro p hp
        rw [norm_div, Complex.norm_natCast, div_pow]
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact (pow_le_pow_left₀ (norm_nonneg _) (hF p (hprime p hp).pos) 2).trans_eq
          (by norm_num)
      _ ≤ _ := mrt_finite_reciprocal_square_tail S hY.le (fun p hp => (hbin p hp).1)
  have hm := mrt_prime_large_set_measure S (fun p => F p/(p:ℂ)) (2*⌈Y⌉₊) r
    hprime hcap hT hV hE hET hlarge
  apply hm.trans
  unfold mrtShortPrimeLargeCost
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sum_nonneg (fun _ _ => sq_nonneg _)) hmass r) (by positivity)

theorem mrt_no_small_log_measure (V : ℕ → Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (J j : ℕ) (hj : j < J)
    {P Q η : ℝ} (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hres : 2 ≤ mrtBaseResolution P Q η)
    (hprime : ∀ p ∈ V (j+1), p.Prime)
    (hrange : ∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) (r : ℕ) {T : ℝ} (hT : 0 < T) :
    (∫ _t in Set.Ioc (-T) T ∩ mrtNoSmallBand (mrtLogFamilyBins P Q η)
      (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J, (1:ℝ)) ≤
      ∑ k ∈ mrtLogFamilyBins P Q η j,
        mrtShortPrimeLargeCost (mrtPrimeLogLower (mrtResolution P Q η (j+1)) k)
          (mrtLogFamilyThreshold P Q η j k) T r := by
  let H := mrtResolution P Q η (j+1)
  let K := mrtLogFamilyBins P Q η j
  let E := Set.Ioc (-T) T ∩ mrtNoSmallBand (mrtLogFamilyBins P Q η)
    (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J
  let B := fun k => {t | mrtLogFamilyThreshold P Q η j k <
    ‖mrtLogFamilyPolynomial V F P Q η j k t‖}
  have hH : 2 ≤ H := by
    have hj1 : (1:ℝ) ≤ (j+1:ℕ) := by exact_mod_cast (show 1 ≤ j+1 by omega)
    have hs : 1 ≤ ((j+1:ℕ):ℝ)^2 := one_le_pow₀ hj1
    dsimp [H, mrtResolution]
    nlinarith [mrtBaseResolution_pos P Q η]
  have hd := mrt_log_bin_prime_data (V (j+1)) hH (Real.exp_pos _) hprime hrange
  have hl : 2 ≤ Real.log (mrtBandLower P Q (j+1)) := by
    have hp := mrt_log_band_lower_fourth P Q (j+1) (by omega) (by linarith) hQ
    have hj1 : (1:ℝ) ≤ (j+1:ℕ) := by exact_mod_cast (show 1 ≤ j+1 by omega)
    have hs : 1 ≤ ((j+1:ℕ):ℝ)^4 := one_le_pow₀ hj1
    nlinarith
  have hE : MeasurableSet E := measurableSet_Ioc.inter
    (mrt_no_small_band_measurable _ _ _
      (fun _ _ => mrt_log_prime_polynomial_continuous _ _ _ _) _)
  have hi : IntegrableOn (fun _ : ℝ => (1:ℝ)) E := by
    have hh := mrt_continuous_square_integrable
      (F := fun _ : ℝ => (1:ℂ)) (E := E) continuous_const hT.le Set.inter_subset_left
    simpa only [norm_one, one_pow] using hh
  have hc := mrt_nonnegative_integral_cover K B
    (fun k _ => (isOpen_lt continuous_const
      (mrt_log_prime_polynomial_continuous _ _ _ _).norm).measurableSet)
    hE (fun _ => (1:ℝ)) hi (fun _ _ => by norm_num) (fun t ht =>
      mrt_no_small_band_large_witness (mrtLogFamilyBins P Q η)
        (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) hj ht.2)
  apply hc.trans
  apply sum_le_sum
  intro k hk
  have hY : 1 < mrtPrimeLogLower H k :=
    mrt_log_bin_lower_gt_one hH (Real.exp_pos _) hl hk
  apply mrt_short_prime_large_measure
    ((V (j+1)).filter (fun p => mrtPrimeLogBin H p = k))
    (fun p hp => hprime p (mem_filter.mp hp).1) hY
    (fun p hp => by
      have hh := hd.2 p (mem_filter.mp hp).1
      have hu := hh.2.trans (mul_le_mul_of_nonneg_right
        (mrt_prime_log_width hH).2.1 (Real.exp_pos _).le)
      simpa only [(mem_filter.mp hp).2] using And.intro hh.1 hu)
    F hF r hT (Real.exp_pos _) (hE.inter
      ((isOpen_lt continuous_const
        (mrt_log_prime_polynomial_continuous _ _ _ _).norm).measurableSet))
    (Set.inter_subset_left.trans Set.inter_subset_left) (fun t ht => ht.2.le)

end TwoPointCorrelations

end OAI
