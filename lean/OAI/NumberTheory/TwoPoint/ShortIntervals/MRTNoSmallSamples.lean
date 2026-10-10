import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallMeasure

namespace OAI

/-! The actual last-band witness controls the number of one-separated
samples in the no-small class. The moment order is left free for optimization. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical

noncomputable def mrtShortPrimeSampleCost (Y V T : ℝ) (r : ℕ) : ℝ :=
  (8*Real.exp 1*(T+1+((2*⌈Y⌉₊)^r:ℕ)) *
    (2+(Real.log ((2*⌈Y⌉₊)^r:ℕ))^2) * (r.factorial:ℝ)*(2/Y)^r)/V^(2*r)

theorem mrt_short_prime_large_samples (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) {Y V T : ℝ} (hY : 1 < Y)
    (hbin : ∀ p ∈ P, Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y)
    (F : ℕ → ℂ) (hF : OneBounded F) (r : ℕ) (hT : 0 ≤ T) (hV : 0 < V)
    (S : Finset ℝ) (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t ≠ s → 1 ≤ |t-s|)
    (hlarge : ∀ t ∈ S, V ≤ ‖mrtExponentialPolynomial P
      (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖) :
    (S.card:ℝ) ≤ mrtShortPrimeSampleCost Y V T r := by
  have hcap (p : ℕ) (hp : p ∈ P) : p ≤ 2*⌈Y⌉₊ := by
    have hh := (hbin p hp).2.trans
      (mul_le_mul_of_nonneg_left (Nat.le_ceil Y) (by norm_num : (0:ℝ) ≤ 2))
    exact_mod_cast hh
  have hmass : (∑ p ∈ P, ‖F p/(p:ℂ)‖^2) ≤ 2/Y := by
    calc
      _ ≤ ∑ p ∈ P, 1/(p:ℝ)^2 := by
        apply sum_le_sum
        intro p hp
        rw [norm_div, Complex.norm_natCast, div_pow]
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact (pow_le_pow_left₀ (norm_nonneg _) (hF p (hprime p hp).pos) 2).trans_eq
          (by norm_num)
      _ ≤ _ := mrt_finite_reciprocal_square_tail P hY.le (fun p hp => (hbin p hp).1)
  apply (mrt_prime_large_values P (fun p => F p/(p:ℂ)) (2*⌈Y⌉₊) r
    hprime hcap S hT hV hS hsep hlarge).trans
  unfold mrtShortPrimeSampleCost
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sum_nonneg (fun _ _ => sq_nonneg _)) hmass r) (by positivity)

theorem mrt_no_small_log_samples (V : ℕ → Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (J j : ℕ) (hj : j < J)
    {P Q η : ℝ} (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hres : 2 ≤ mrtBaseResolution P Q η)
    (hprime : ∀ p ∈ V (j+1), p.Prime)
    (hrange : ∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) (r : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (S : Finset ℝ) (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t ≠ s → 1 ≤ |t-s|)
    (hno : ∀ t ∈ S, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q η)
      (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J) :
    (S.card:ℝ) ≤ ∑ k ∈ mrtLogFamilyBins P Q η j,
      mrtShortPrimeSampleCost (mrtPrimeLogLower (mrtResolution P Q η (j+1)) k)
        (mrtLogFamilyThreshold P Q η j k) T r := by
  let H := mrtResolution P Q η (j+1)
  let K := mrtLogFamilyBins P Q η j
  let S' := fun k => S.filter (fun t => mrtLogFamilyThreshold P Q η j k <
    ‖mrtLogFamilyPolynomial V F P Q η j k t‖)
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
  have hcover : S ⊆ K.biUnion S' := by
    intro t ht
    obtain ⟨k,hk,htk⟩ := mrt_no_small_band_large_witness
      (mrtLogFamilyBins P Q η) (mrtLogFamilyPolynomial V F P Q η)
      (mrtLogFamilyThreshold P Q η) hj (hno t ht)
    exact mem_biUnion.mpr ⟨k,hk,mem_filter.mpr ⟨ht,htk⟩⟩
  have hcard : (S.card:ℝ) ≤ ∑ k ∈ K, ((S' k).card:ℝ) := by
    exact_mod_cast (card_le_card hcover).trans (card_biUnion_le)
  apply hcard.trans
  apply sum_le_sum
  intro k hk
  have hY : 1 < mrtPrimeLogLower H k :=
    mrt_log_bin_lower_gt_one hH (Real.exp_pos _) hl hk
  apply mrt_short_prime_large_samples
    ((V (j+1)).filter (fun p => mrtPrimeLogBin H p = k))
    (fun p hp => hprime p (mem_filter.mp hp).1) hY
    (fun p hp => by
      have hh := hd.2 p (mem_filter.mp hp).1
      have hu := hh.2.trans (mul_le_mul_of_nonneg_right
        (mrt_prime_log_width hH).2.1 (Real.exp_pos _).le)
      simpa only [(mem_filter.mp hp).2] using And.intro hh.1 hu)
    F hF r hT (Real.exp_pos _) (S' k)
    (fun t ht => hS t (mem_filter.mp ht).1)
    (fun t ht s hs hts => hsep t (mem_filter.mp ht).1 s (mem_filter.mp hs).1 hts)
    (fun _ ht => (mem_filter.mp ht).2.le)

end TwoPointCorrelations

end OAI
