import OAI.NumberTheory.JointDickman.Amplification.CountMaskDistance

namespace OAI

/-! # Near-zero cancellation for the actual soft-masked cofactor means -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology ComplexConjugate

lemma halasz_phase_factor_decay (t x : ℝ) :
    ‖halaszPowerPhase t x / (1+(-t:ℂ)*Complex.I)‖ ≤ 2/(1+|t|) := by
  have h1 : 1 ≤ ‖(1:ℂ)+(-t:ℂ)*Complex.I‖ := by
    simpa [Complex.mul_re] using Complex.re_le_norm ((1:ℂ)+(-t:ℂ)*Complex.I)
  have ht : |t| ≤ ‖(1:ℂ)+(-t:ℂ)*Complex.I‖ := by
    simpa [Complex.mul_im] using Complex.abs_im_le_norm ((1:ℂ)+(-t:ℂ)*Complex.I)
  rw [norm_div, halasz_power_phase_norm]
  apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
  linarith

lemma halasz_phase_mean_norm (F : ℕ → ℂ) (hF : OneBounded F) (t : ℝ) (N : ℕ) :
    ‖halaszPhaseMean F t N‖ ≤ N := by
  unfold halaszPhaseMean
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖F n * halaszPowerPhase t n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc 1 N, (1:ℝ) := by
      apply sum_le_sum
      intro n hn
      simpa only [norm_mul, halasz_power_phase_norm, mul_one] using hF n (mem_Icc.mp hn).1
    _ = _ := by simp

/-- Near-twist renormalization gives reciprocal-frequency
cancellation around zero, uniformly in the deleted small-prime set. -/
theorem near_zero_masked_mean : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ F : ℕ → ℂ,
      F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      squaredDistance F (mrtArchimedeanTwist 0) N ≤ Real.log (Real.log N)/8 →
      ∀ t : ℝ, |t| ≤ (Real.log N)^((1:ℝ)/16) →
      ‖halaszPhaseMean (mrtMissingCoefficient F Q) t N‖ ≤
        (2/(1+|t|)+C*(Real.log N)^(-(1:ℝ)/16))*N := by
  let C := 36*(halaszPrimePowerLogConstant+1)*Real.exp 8
  have hC : 0 < C := by dsimp [C, halaszPrimePowerLogConstant]; positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [halasz_near_renormalization] with N hN
  intro F hF1 hFm hFb Q hQ hcut hdist t ht
  have hh := hN F hF1 hFm hFb Q hQ hcut 0 hdist t ht
  have hzero : halaszTwistedFunction (mrtMissingCoefficient F Q) 0 =
      mrtMissingCoefficient F Q := by
    funext n
    simp only [halaszTwistedFunction, mrtArchimedeanTwist, zero_mul,
      Complex.ofReal_zero, Complex.exp_zero, map_one, mul_one]
  dsimp only at hh
  rw [hzero] at hh
  have hm := halasz_phase_mean_norm (mrtMissingCoefficient F Q)
    (mrtMissingCoefficient_oneBounded F hFb Q) 0 N
  have hmain : ‖(halaszPowerPhase t N/(1+(-t:ℂ)*Complex.I))*
      halaszPhaseMean (mrtMissingCoefficient F Q) 0 N‖ ≤ 2/(1+|t|)*N := by
    rw [norm_mul]
    exact mul_le_mul (halasz_phase_factor_decay t N) hm (norm_nonneg _) (by positivity)
  have hnorm := norm_sub_le_norm_sub_add_norm_sub
    (halaszPhaseMean (mrtMissingCoefficient F Q) t N)
    ((halaszPowerPhase t N/(1+(-t:ℂ)*Complex.I))*
      halaszPhaseMean (mrtMissingCoefficient F Q) 0 N) 0
  simp only [sub_zero] at hnorm
  change ‖halaszPhaseMean (mrtMissingCoefficient F Q) t N - _‖ ≤
    C*N*(Real.log N)^(-(1:ℝ)/16) at hh
  nlinarith

/-- The reciprocal prime-count denominator is handled by its exact
integral of multiplicative soft masks, with no loss near frequency zero. -/
theorem near_zero_count_prefix : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ F : ℕ → ℂ,
      F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ Q P : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
      (∀ p ∈ Q, (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      squaredDistance F (mrtArchimedeanTwist 0) N +
        (∑ p ∈ P, 1/(p:ℝ)) ≤ Real.log (Real.log N)/8 →
      ∀ t : ℝ, |t| ≤ (Real.log N)^((1:ℝ)/16) →
      ‖∑ n ∈ Icc 1 N,
        (mrtMissingCoefficient F Q n * conj (mrtArchimedeanTwist t n))/
          ((finitePrimeDivisorCount P n:ℂ)+1)‖ ≤
        (2/(1+|t|)+C*(Real.log N)^(-(1:ℝ)/16))*N := by
  obtain ⟨C,hC,hmean⟩ := near_zero_masked_mean
  refine ⟨C,hC,?_⟩
  filter_upwards [hmean] with N hN
  intro F hF1 hFm hFb Q P hQ hP hcut hdist t ht
  apply mrt_reciprocal_count_polynomial_bound (Icc 1 N) P
    (fun n => mrtMissingCoefficient F Q n * conj (mrtArchimedeanTwist t n))
  intro u hu hu1
  let G := mrtCountMaskedCoefficient F P u
  have hG1 : G 1 = 1 := by
    simp only [G,mrtCountMaskedCoefficient,hF1,mrtCountMask_one P hP,Complex.ofReal_one,mul_one]
  have hGm : Multiplicative G := hFm.mrtCountMaskedCoefficient P hP u
  have hGb : OneBounded G := hFb.mrtCountMaskedCoefficient P hu hu1
  have hd : squaredDistance G (mrtArchimedeanTwist 0) N ≤ Real.log (Real.log N)/8 :=
    (count_mask_distance_zero_le F hFb P hP hu hu1 N).trans hdist
  have hh := hN G hG1 hGm hGb Q hQ hcut hd t ht
  convert hh using 1
  congr 1
  apply sum_congr rfl
  intro n _
  simp only [G, mrtCountMaskedCoefficient, mrtMissingCoefficient,
    halaszPowerPhase, mrtArchimedeanTwist, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, Complex.ofReal_neg, neg_mul]
  ring

end JointDickman

end OAI
