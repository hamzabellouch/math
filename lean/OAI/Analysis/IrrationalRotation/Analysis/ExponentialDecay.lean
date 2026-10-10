import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

open Filter Topology
open scoped BigOperators ENNReal

namespace Invariant233

theorem prod_le_exp_sum_truncated_log {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (M : ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, f i) ≤
      Real.exp (∑ i ∈ s, Real.log (max (f i) (Real.exp (-M)))) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀ hf
  intro i hi
  rw [Real.exp_log (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _))]
  exact le_max_left _ _

theorem prod_le_exp_of_sum_truncated_log_le {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (M B : ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hs : (∑ i ∈ s, Real.log (max (f i) (Real.exp (-M)))) ≤ B) :
    (∏ i ∈ s, f i) ≤ Real.exp B :=
  (prod_le_exp_sum_truncated_log s f M hf).trans (Real.exp_le_exp.mpr hs)

theorem tendsto_root_zero_of_exponential_decay (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n)
    (hdecay : ∀ a : ℝ, 0 < a → ∀ᶠ n : ℕ in atTop,
      u n ≤ Real.exp (-a * (n : ℝ))) :
    Tendsto (fun n : ℕ => (u n) ^ (1 / (n : ℝ))) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall fun n =>
      hc.trans_le (Real.rpow_nonneg (hu n) _)
  · intro ε hε
    have he : ∀ᶠ a : ℝ in atTop, Real.exp (-a) < ε :=
      (tendsto_order.mp Real.tendsto_exp_neg_atTop_nhds_zero).2 ε hε
    obtain ⟨a, ha, hae⟩ := ((eventually_gt_atTop (0 : ℝ)).and he).exists
    filter_upwards [hdecay a ha, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hnzero : n ≠ 0 := Nat.ne_of_gt hnpos
    have hroot := Real.rpow_le_rpow (hu n) hn (by positivity : 0 ≤ 1 / (n : ℝ))
    have heq : Real.exp (-a * (n : ℝ)) = (Real.exp (-a)) ^ n := by
      rw [mul_comm, Real.exp_nat_mul]
    rw [heq, one_div, Real.pow_rpow_inv_natCast (Real.exp_nonneg _) hnzero] at hroot
    simpa only [one_div] using hroot.trans_lt hae

theorem norm_quasinilpotent_of_exponential_decay {A : Type*} [NormedRing A]
    (T : A)
    (hdecay : ∀ a : ℝ, 0 < a → ∀ᶠ n : ℕ in atTop,
      ‖T ^ n‖ ≤ Real.exp (-a * (n : ℝ))) :
    Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) :=
  tendsto_root_zero_of_exponential_decay (fun n => ‖T ^ n‖)
    (fun _ => norm_nonneg _) hdecay

theorem spectralRadius_zero_of_norm_root_tendsto_zero {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (T : A)
    (hroot : Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)) :
    spectralRadius ℂ T = 0 := by
  have hzero : Tendsto
      (fun n : ℕ => ENNReal.ofReal (‖T ^ n‖ ^ (1 / (n : ℝ))))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hroot
  exact tendsto_nhds_unique
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius T) hzero

theorem spectralRadius_zero_of_exponential_decay {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (T : A)
    (hdecay : ∀ a : ℝ, 0 < a → ∀ᶠ n : ℕ in atTop,
      ‖T ^ n‖ ≤ Real.exp (-a * (n : ℝ))) :
    spectralRadius ℂ T = 0 :=
  spectralRadius_zero_of_norm_root_tendsto_zero T
    (norm_quasinilpotent_of_exponential_decay T hdecay)

theorem spectrum_subset_zero_of_spectralRadius_zero {𝕜 A : Type*}
    [NormedField 𝕜] [Ring A] [Algebra 𝕜 A] (T : A)
    (hzero : spectralRadius 𝕜 T = 0) :
    spectrum 𝕜 T ⊆ {0} := by
  intro z hz
  have hnorm : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius 𝕜 T := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂ (f := fun scalar (_ : scalar ∈ spectrum 𝕜 T) =>
      (‖scalar‖₊ : ℝ≥0∞)) z hz
  rw [hzero] at hnorm
  simpa using hnorm

theorem spectrum_eq_zero_of_spectralRadius_zero {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (T : A)
    (hzero : spectralRadius ℂ T = 0) : spectrum ℂ T = {0} := by
  have hsub := spectrum_subset_zero_of_spectralRadius_zero T hzero
  apply Set.Subset.antisymm hsub
  obtain ⟨z, hz⟩ := spectrum.nonempty T
  have hz0 : z = 0 := hsub hz
  simpa only [Set.singleton_subset_iff, hz0] using hz

theorem spectrum_eq_zero_of_norm_root_tendsto_zero {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (T : A)
    (hroot : Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)) :
    spectrum ℂ T = {0} :=
  spectrum_eq_zero_of_spectralRadius_zero T
    (spectralRadius_zero_of_norm_root_tendsto_zero T hroot)

theorem spectrum_eq_zero_of_exponential_decay {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (T : A)
    (hdecay : ∀ a : ℝ, 0 < a → ∀ᶠ n : ℕ in atTop,
      ‖T ^ n‖ ≤ Real.exp (-a * (n : ℝ))) :
    spectrum ℂ T = {0} :=
  spectrum_eq_zero_of_spectralRadius_zero T
    (spectralRadius_zero_of_exponential_decay T hdecay)

end Invariant233

end OAI
