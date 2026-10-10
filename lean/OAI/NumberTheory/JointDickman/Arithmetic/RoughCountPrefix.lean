import OAI.NumberTheory.JointDickman.Amplification.MiddleCountPrefix
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeAgreementZeroDistance
import OAI.NumberTheory.JointDickman.Amplification.HalaszArithmetic

namespace OAI

/-! # Joining near-zero and middle-frequency reciprocal-count estimates -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology ComplexConjugate

lemma halaszPowerPhase_eq_conj_twist (t : ℝ) (n : ℕ) :
    halaszPowerPhase t n = conj (mrtArchimedeanTwist t n) := by
  simp only [halaszPowerPhase,mrtArchimedeanTwist,← Complex.exp_conj,
    map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg,Complex.ofReal_neg,neg_mul]

/-- Cancellation is uniform outside one fixed bounded neighborhood of zero.
The coefficients may vary with the cutoff, subject to literal small-prime
power agreement. -/
theorem rough_count_prefix_away_zero {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ T : ℝ, 0 < T ∧
    ∀ᶠ N : ℕ in atTop, ∀ (f : ArithmeticFunction ℂ) (P : Finset ℕ),
      f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N:ℝ)^c → p^k ≤ N → f (p^k) = 1) →
      (∀ p ∈ P, p.Prime ∧ (N:ℝ)^c < (p:ℝ) ∧ (p:ℝ) ≤ N) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ 4*(Real.log N)^8 →
      ‖∑ n ∈ Icc 1 N, (f n*halaszPowerPhase t n)/
        ((finitePrimeDivisorCount P n:ℂ)+1)‖/(N:ℝ) ≤ ε := by
  obtain ⟨C,hC,hnear⟩ := near_zero_count_prefix
  obtain ⟨D,hD,hzero⟩ := prime_agreement_zero_distance_bounded hc hc1 ∅
  let M : ℝ := -Real.log c+1
  let T : ℝ := max 1 (4/ε)
  have hT : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)
  refine ⟨T,hT,?_⟩
  have hn : Tendsto (fun N : ℕ => (Real.log N)^(-(1:ℝ)/16)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/16)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [Function.comp_def,neg_div] using hh
  have herror : ∀ᶠ N : ℕ in atTop, C*(Real.log N)^(-(1:ℝ)/16) ≤ ε/2 :=
    (hn.const_mul C).eventually (eventually_le_nhds (by simpa using (show 0<ε/2 by positivity)))
  have hloglog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [hnear,middle_frequency_count_prefix hc hc1 hε,herror,
    tendsto_natCast_atTop_atTop.eventually hzero,
    tendsto_natCast_atTop_atTop.eventually (rough_prime_mass_bounded hc hc1),
    hloglog.eventually (eventually_ge_atTop (8*(D+M))),eventually_ge_atTop 1]
    with N hnearN hmiddleN herrorN hzeroN hmassN hlogN hN1
  intro f P hf hfb hsmall hP t htlo hthi
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hFm : Multiplicative (f : ℕ → ℂ) := fun x y _ _ hxy => hf.2 hxy
  have hFb : OneBounded (f : ℕ → ℂ) := fun n _ => hfb n
  by_cases ht : |t| ≤ (Real.log N)^((1:ℝ)/16)
  · have hpow : (N:ℝ)^c ≤ N := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1 : (1:ℝ)≤N) hc1
    have hdist : squaredDistance f (mrtArchimedeanTwist 0) N ≤ D := by
      rw [halasz_distance_eq]
      apply hzeroN f hfb
      intro p hp _ hpc
      simpa only [pow_one] using hsmall p 1 hp hpc (by rw [pow_one]; exact_mod_cast hpc.trans hpow)
    have hmass : (∑ p ∈ P, 1/(p:ℝ)) ≤ M := hmassN P hP
    change 8*(D+M) ≤ Real.log (Real.log (N:ℝ)) at hlogN
    have hd : squaredDistance f (mrtArchimedeanTwist 0) N +
        (∑ p ∈ P, 1/(p:ℝ)) ≤ Real.log (Real.log N)/8 := by linarith
    have hh := hnearN f hf.1 hFm hFb ∅ P (by simp) (fun p hp => (hP p hp).1)
      (by simp) hd t ht
    have he : mrtMissingCoefficient f ∅ = (f : ℕ → ℂ) := by
      funext n
      simp [mrtMissingCoefficient,mrtPrimeMask,mrtPrimeAvoids]
    rw [he] at hh
    simp_rw [← halaszPowerPhase_eq_conj_twist] at hh
    apply (div_le_iff₀ hNp).mpr
    apply hh.trans
    have hmain : 2/(1+|t|) ≤ ε/2 := by
      apply (div_le_iff₀ (by positivity : 0<1+|t|)).mpr
      have hlow : 4/ε ≤ |t| := (le_max_right _ _).trans htlo
      have hm := (div_le_iff₀ hε).mp hlow
      nlinarith
    exact mul_le_mul_of_nonneg_right (by linarith) hNp.le
  · exact hmiddleN f P hf.1 hFm hFb hsmall (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1⟩)
      t (le_of_not_ge ht) hthi

end JointDickman

end OAI
