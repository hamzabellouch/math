import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogClassData

namespace OAI

/-! The first frequency-class estimate for actual logarithmic prime bins.
Prime membership, bin width, and the complete scalar sum are derived here. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped Classical

theorem mrt_first_log_class_energy {ι : Type*} (J : Finset ι) (V : ι → Finset ℕ)
    (hprime : ∀ j ∈ J, ∀ p ∈ V j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) V) {j : ι} (hj : j ∈ J)
    {P Q η : ℝ} (hP : 1 ≤ P) (hQ0 : 0 < Q) (hQ : 1 ≤ Real.log Q)
    (hη : 0 ≤ η) (hη' : η ≤ 1/12)
    (hH : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ p ∈ V j, P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Q)
    {N : ℕ} (hN : 0 < N) (hsize : 2*Q ≤ (N:ℝ))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in Ioc (-T) T ∩ mrtLogSmallSet (V j) F (mrtBaseResolution P Q η)
        (mrtLogBins (mrtBaseResolution P Q η) P Q) (mrtFrequencyExponent η 0),
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient J V F) N t‖^2) ≤
      2816*Real.exp 1*(T/N+1)*
        ((∑ p ∈ V j, 1/(p:ℝ)^2)+(∑ p ∈ V j, 1/(p:ℝ)^2)^2+
          2/mrtBaseResolution P Q η) +
      1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹ := by
  let H := mrtBaseResolution P Q η
  let K := mrtLogBins H P Q
  let E := Ioc (-T) T ∩ mrtLogSmallSet (V j) F H K (mrtFrequencyExponent η 0)
  have hH0 : 0 < H := mrtBaseResolution_pos P Q η
  have hQ1 : 1 ≤ Q := by
    have hh := Real.one_le_exp (by linarith : 0 ≤ Real.log Q)
    simpa only [Real.exp_log hQ0] using hh
  have hdata := mrt_log_bin_prime_data (V j) hH (by linarith : 0 < P)
    (hprime j hj) hrange
  have hwidth := mrt_prime_log_width hH
  have hupper (k : ℕ) (hk : k ∈ K) : 2 ≤ (N:ℝ)/mrtPrimeLogLower H k := by
    have hkQ : mrtPrimeLogLower H k ≤ Q :=
      mrt_prime_log_lower_le_upper hH0 hQ1 (mem_Icc.mp hk).2
    exact (le_div_iff₀ (Real.exp_pos _)).mpr
      ((mul_le_mul_of_nonneg_left hkQ (by norm_num : (0:ℝ) ≤ 2)).trans hsize)
  have hb := mrt_general_typical_small_prime_energy J V hprime hdis hj K
    (mrtPrimeLogBin H) hdata.1 (mrtPrimeLogLower H) hN hwidth.1 hwidth.2.1 hdata.2
    (fun k _ => mrt_prime_log_lower_one hH0 k) hupper F hF hFb hT E
    inter_subset_left (fun k => Real.exp (-mrtFrequencyExponent η 0 *
      Real.log (mrtPrimeLogLower H k))) (fun k hk t ht => ht.2 k hk)
  have hs := mrt_first_bin_moment_sum (N := (N:ℝ)) (T := T) hη hη' hP hQ0 hQ hH
    (by exact_mod_cast hN) hT.le
  change (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J V F) N t‖^2) ≤ _
  apply hb.trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (by linarith [hwidth.2.2]) (by positivity)) hs

end TwoPointCorrelations

end OAI
