import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogClassData

namespace OAI

/-! Actual adjacent logarithmic prime bins give the summable later-class
energy bound. The preceding large witness is part of the frequency set. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped Classical

noncomputable def mrtLaterLogClass (S₀ S₁ : Finset ℕ) (F : ℕ → ℂ)
    (P Q η : ℝ) (j : ℕ) (T : ℝ) : Set ℝ :=
  Ioc (-T) T ∩
    (mrtLogSmallSet S₁ F (mrtResolution P Q η (j+2))
      (mrtLogBins (mrtResolution P Q η (j+2))
        (mrtBandLower P Q (j+2)) (mrtBandUpper Q (j+2)))
      (mrtFrequencyExponent η (j+1)) ∩
    mrtLogLargeSet S₀ F (mrtResolution P Q η (j+1))
      (mrtLogBins (mrtResolution P Q η (j+1))
        (mrtBandLower P Q (j+1)) (mrtBandUpper Q (j+1)))
      (mrtFrequencyExponent η j))

theorem mrt_later_log_class_energy {ι : Type*} (J : Finset ι) (V : ι → Finset ℕ)
    (hprime : ∀ ν ∈ J, ∀ p ∈ V ν, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) V) {ν : ι} (hν : ν ∈ J)
    (S₀ : Finset ℕ) (hprime₀ : ∀ p ∈ S₀, p.Prime)
    {P Q η : ℝ} (hP0 : 0 < P) (hP : 2 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) (hPQ : Real.log P ≤ Real.log Q)
    (hη : 0 < η) (hη' : η ≤ 1/6)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (j : ℕ)
    (hrange₀ : ∀ p ∈ S₀, mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1))
    (hrange₁ : ∀ p ∈ V ν, mrtBandLower P Q (j+2) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+2))
    {N : ℕ} (hN : 0 < N) (F : ℕ → ℂ)
    (hF : Multiplicative F) (hFb : OneBounded F) {T : ℝ} (hT : 0 < T) :
    (∫ t in mrtLaterLogClass S₀ (V ν) F P Q η j T,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient J V F) N t‖^2) ≤
      2816*Real.exp 1*(T/N+1)*
        ((∑ p ∈ V ν, 1/(p:ℝ)^2)+(∑ p ∈ V ν, 1/(p:ℝ)^2)^2+
          2/mrtResolution P Q η (j+2)) +
      (T/N+1)*P⁻¹*(((j:ℝ)+2)^2)⁻¹ := by
  let H₀ := mrtResolution P Q η (j+1)
  let H₁ := mrtResolution P Q η (j+2)
  let B := mrtLogBins H₀ (mrtBandLower P Q (j+1)) (mrtBandUpper Q (j+1))
  let K := mrtLogBins H₁ (mrtBandLower P Q (j+2)) (mrtBandUpper Q (j+2))
  let E := mrtLaterLogClass S₀ (V ν) F P Q η j T
  have hres (k : ℕ) (hk : 1 ≤ k) : 2 ≤ mrtResolution P Q η k := by
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hs : 1 ≤ (k:ℝ)^2 := one_le_pow₀ hk1
    unfold mrtResolution
    nlinarith [mrtBaseResolution_pos P Q η]
  have hH₀ : 2 ≤ H₀ := hres _ (by omega)
  have hH₁ : 2 ≤ H₁ := hres _ (by omega)
  have hlowlog (k : ℕ) (hk : 1 ≤ k) : 2 ≤ Real.log (mrtBandLower P Q k) := by
    have hh := mrt_log_band_lower_fourth P Q k hk (by linarith) hQ
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hp : 1 ≤ (k:ℝ)^4 := one_le_pow₀ hk1
    nlinarith
  have hd₁ := mrt_log_bin_prime_data (V ν) hH₁ (Real.exp_pos _)
    (hprime ν hν) hrange₁
  have hd₀ := mrt_log_bin_prime_data S₀ hH₀ (Real.exp_pos _) hprime₀ hrange₀
  have hwidth := mrt_prime_log_width hH₁
  have hY (b : ℕ) (hb : b ∈ B) : 1 < mrtPrimeLogLower H₀ b :=
    mrt_log_bin_lower_gt_one hH₀ (Real.exp_pos _) (hlowlog _ (by omega)) hb
  have hp₀ (b : ℕ) (_hb : b ∈ B) (p : ℕ)
      (hp : p ∈ S₀.filter (fun p => mrtPrimeLogBin H₀ p = b)) : p.Prime :=
    hprime₀ p (mem_filter.mp hp).1
  have hbin₀ (b : ℕ) (_hb : b ∈ B) (p : ℕ)
      (hp : p ∈ S₀.filter (fun p => mrtPrimeLogBin H₀ p = b)) :
      mrtPrimeLogLower H₀ b ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*mrtPrimeLogLower H₀ b := by
    have hx := hd₀.2 p (mem_filter.mp hp).1
    have hh := And.intro hx.1 (hx.2.trans (mul_le_mul_of_nonneg_right
      (mrt_prime_log_width hH₀).2.1 (Real.exp_pos _).le))
    simpa only [(mem_filter.mp hp).2] using hh
  have hEm : MeasurableSet E := measurableSet_Ioc.inter
    ((mrt_log_small_set_measurable _ _ _ _ _).inter
      (mrt_log_large_set_measurable _ _ _ _ _))
  have hb := mrt_general_typical_witnessed_energy J V hprime hdis hν K
    (mrtPrimeLogBin H₁) hd₁.1 (mrtPrimeLogLower H₁) hN hwidth.1 hwidth.2.1 hd₁.2
    (fun k _ => mrt_prime_log_lower_one (by linarith) k) F hF hFb B
    (fun b => S₀.filter (fun p => mrtPrimeLogBin H₀ p = b))
    (mrtPrimeLogLower H₀) hY hp₀ hbin₀
    (fun b => Real.exp (-mrtFrequencyExponent η j*Real.log (mrtPrimeLogLower H₀ b)))
    (fun _ _ => Real.exp_pos _) hT hEm inter_subset_left
    (fun k => Real.exp (-mrtFrequencyExponent η (j+1)*Real.log (mrtPrimeLogLower H₁ k)))
    (fun k hk t ht => ht.2.1 k hk) (fun t ht => by
      obtain ⟨b, hb, hl⟩ := ht.2.2
      exact ⟨b, hb, hl.le⟩)
  have hs := mrt_later_bin_moment_sum hη hη' j hP0 hP hQ hPQ hbudget hH
    (div_nonneg hT.le (Nat.cast_nonneg N))
  have hcost : (2 * ∑ b ∈ B, (K.card:ℝ) * ∑ k ∈ K,
      (Real.exp (-mrtFrequencyExponent η (j+1)*Real.log (mrtPrimeLogLower H₁ k)))^2 *
        ((16*Real.exp 10*(T/N+(2:ℝ)^(mrtAmplificationOrder ⌈mrtPrimeLogLower H₀ b⌉₊
          (mrtPrimeLogLower H₁ k)+1)*⌈mrtPrimeLogLower H₀ b⌉₊)*
          ((mrtAmplificationOrder ⌈mrtPrimeLogLower H₀ b⌉₊ (mrtPrimeLogLower H₁ k)).factorial:ℝ)^2)/
          (Real.exp (-mrtFrequencyExponent η j*Real.log (mrtPrimeLogLower H₀ b)))^
            (2*mrtAmplificationOrder ⌈mrtPrimeLogLower H₀ b⌉₊ (mrtPrimeLogLower H₁ k)))) ≤
      (T/N+1)*P⁻¹*(((j:ℝ)+2)^2)⁻¹ := hs
  change (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J V F) N t‖^2) ≤ _
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left (by linarith [hwidth.2.2]) (by positivity)) hcost)

end TwoPointCorrelations

end OAI
