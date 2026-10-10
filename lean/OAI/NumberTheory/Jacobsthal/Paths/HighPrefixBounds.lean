import OAI.NumberTheory.Jacobsthal.Probability.HighPrefixKernel

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.HighPrefixBounds

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
open WeightedKernelMass HarmonicLongPrefixes HighPrefixState
open HighPrefixKernel

noncomputable def lowHighMass (ell S B R K : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, (kernel ell S ^ n) (initial S B R) {z | z.2.2=true ∧ z.2.1≤K}

noncomputable def reward (c : ℝ) (z : State) : ℝ≥0∞ :=
  if z.2.2=true ∧ 0≤z.2.1 then ENNReal.ofReal (Real.exp (-c*z.2.1)) else 0

lemma reward_measurable (c : ℝ) : Measurable (reward c) := by
  have hf : Measurable (fun z : State => z.2.2) := measurable_snd.comp measurable_snd
  have hr : Measurable (fun z : State => z.2.1) := measurable_fst.comp measurable_snd
  have hs : MeasurableSet {z : State | z.2.2=true ∧ 0≤z.2.1} := by
    have hz : MeasurableSet {z : State | (0:ℝ)≤z.2.1} := measurableSet_le measurable_const hr
    exact (hf (measurableSet_singleton true)).inter hz
  exact Measurable.ite hs (ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_const.mul hr))) measurable_const

noncomputable def rewardedHighMass (ell S B R c : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ∫⁻ z, reward c z ∂(kernel ell S ^ n) (initial S B R)

lemma reward_le_one {c : ℝ} (hc : 0≤c) (z : State) : reward c z ≤ 1 := by
  unfold reward
  split_ifs with hz
  · calc
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by nlinarith [hz.2]))
      _ = 1 := by simp
  · exact zero_le

lemma low_high_zero {ell S B R K : ℝ} (hell : 0<ell) (hB : ell≤B)
    (n m : ℕ) (hm : (m:ℝ)≤S/2) (hn : n<m) (hK : K≤S*ell/2) :
    (kernel ell S ^ n) (initial S B R) {z | z.2.2=true ∧ z.2.1≤K} = 0 := by
  have hnm : (n:ℝ)<m := by exact_mod_cast hn
  have hnS : (n:ℝ)≤S := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hAE : ∀ᵐ z ∂(kernel ell S ^ n) (initial S B R), ¬(z.2.2=true ∧ z.2.1≤K) := by
    filter_upwards [ae_invariant hell hB S R n hnS] with z hz
    intro hbad
    have hgap := short_high_gap hell n z hz hbad.1 (hnm.le.trans hm)
    exact (not_lt_of_ge (hbad.2.trans hK)) hgap
  simpa only [not_not] using ae_iff.mp hAE

theorem low_high_bound {ell S B R K : ℝ} (hell : 0<ell) (hB : ell≤B)
    (m : ℕ) (hm : (m:ℝ)≤S/2) (hK : K≤S*ell/2) :
    lowHighMass ell S B R K ≤ ((2:ℝ≥0∞)⁻¹)^m*ENNReal.ofReal ((B/ell)^2) := by
  have htail : lowHighMass ell S B R K ≤ tailMass (fun n => mass (kernel ell S) n (initial S B R)) m := by
    apply ENNReal.tsum_le_tsum
    intro n
    by_cases hn : m≤n
    · rw [ite_eq_left hn]
      exact measure_mono (subset_univ _)
    · rw [ite_eq_right hn,low_high_zero hell hB n m hm (Nat.lt_of_not_ge hn) hK]
  exact htail.trans (weighted_tail_bound _ m (weighted_mass hell hB S R))

lemma short_reward_bound {ell S B R c : ℝ} (hell : 0<ell) (hB : ell≤B) (hc : 0≤c)
    (n m : ℕ) (hm : (m:ℝ)≤S/2) (hn : n<m) :
    (∫⁻ z, reward c z ∂(kernel ell S ^ n) (initial S B R)) ≤
      ENNReal.ofReal (Real.exp (-c*(S*ell/2))) * mass (kernel ell S) n (initial S B R) := by
  have hnm : (n:ℝ)<m := by exact_mod_cast hn
  have hnS : (n:ℝ)≤S := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hpoint : ∀ᵐ z ∂(kernel ell S ^ n) (initial S B R),
      reward c z ≤ ENNReal.ofReal (Real.exp (-c*(S*ell/2))) := by
    filter_upwards [ae_invariant hell hB S R n hnS] with z hz
    unfold reward
    split_ifs with hbad
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hgap := short_high_gap hell n z hz hbad.1 (hnm.le.trans hm)
      nlinarith
    · exact zero_le
  exact (lintegral_mono_ae hpoint).trans_eq (lintegral_const _)

theorem rewarded_high_bound {ell S B R c : ℝ} (hell : 0<ell) (hB : ell≤B) (hc : 0≤c)
    (m : ℕ) (hm : (m:ℝ)≤S/2) :
    rewardedHighMass ell S B R c ≤ ((2:ℝ≥0∞)⁻¹)^m*ENNReal.ofReal ((B/ell)^2) +
      ENNReal.ofReal (Real.exp (-c*(S*ell/2))) * ENNReal.ofReal (B/ell) := by
  let a : ℕ → ℝ≥0∞ := fun n => mass (kernel ell S) n (initial S B R)
  let E := ENNReal.ofReal (Real.exp (-c*(S*ell/2)))
  have hp : ∀ n : ℕ, (∫⁻ z, reward c z ∂(kernel ell S ^ n) (initial S B R)) ≤
      (if m≤n then a n else 0) + E*a n := by
    intro n
    by_cases hn : m≤n
    · rw [ite_eq_left hn]
      have hle : (∫⁻ z, reward c z ∂(kernel ell S ^ n) (initial S B R)) ≤ a n := by
        simpa only [lintegral_const,one_mul,a,mass] using! lintegral_mono (fun z => reward_le_one hc z)
      exact hle.trans (le_add_of_nonneg_right zero_le)
    · rw [ite_eq_right hn,zero_add]
      exact short_reward_bound hell hB hc n m hm (Nat.lt_of_not_ge hn)
  calc
    _ ≤ ∑' n : ℕ, ((if m≤n then a n else 0) + E*a n) := ENNReal.tsum_le_tsum hp
    _ = tailMass a m + E*(∑' n : ℕ, a n) := by rw [ENNReal.tsum_add,ENNReal.tsum_mul_left]; rfl
    _ ≤ _ := add_le_add (weighted_tail_bound _ m (weighted_mass hell hB S R))
      (mul_le_mul le_rfl (total_mass hell hB S R) zero_le zero_le)

end ErdosPrimeInputs.HighPrefixBounds

end

end Erdos970

end OAI
