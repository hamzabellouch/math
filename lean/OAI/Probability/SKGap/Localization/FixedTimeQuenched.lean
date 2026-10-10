import Mathlib
import OAI.Probability.SKGap.Localization.PartitionChangeMeasure
import OAI.Probability.SKGap.Stability.FixedTimeAnnealed

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

def fixedTimeFailure (n : ℕ) (j A K ε c ρ t : ℝ) (J : Disorder n) : ℝ :=
  (fixedTimeFailureENN j A K ε c ρ t J).toReal

lemma measurable_fixedTimeFailure (n : ℕ) (j A K ε c ρ t : ℝ) :
    Measurable (fixedTimeFailure n j A K ε c ρ t) :=
  (measurable_fixedTimeFailureENN j A K ε c ρ t).ennreal_toReal

lemma fixedTimeFailure_nonneg (n : ℕ) (j A K ε c ρ t : ℝ) (J : Disorder n) :
    0 ≤ fixedTimeFailure n j A K ε c ρ t J := ENNReal.toReal_nonneg

lemma fixedTimeFailure_le_one (n : ℕ) (j A K ε c ρ t : ℝ) (J : Disorder n) :
    fixedTimeFailure n j A K ε c ρ t J ≤ 1 := by
  exact (ENNReal.toReal_mono ENNReal.one_ne_top
    (fixedTimeFailureENN_le_one j A K ε c ρ t J)).trans_eq ENNReal.toReal_one

lemma ofReal_fixedTimeFailure (n : ℕ) (j A K ε c ρ t : ℝ) (J : Disorder n) :
    ENNReal.ofReal (fixedTimeFailure n j A K ε c ρ t J) = fixedTimeFailureENN j A K ε c ρ t J :=
  ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
    (fixedTimeFailureENN_le_one j A K ε c ρ t J))

lemma disorder_partition_integrable (β : ℝ) (n : ℕ) :
    Integrable (fun J : Disorder n=>partition J 0) (disorderLaw β n) := by
  rw [← (gaussian_disorder_hasLaw β n).map_eq]
  apply (integrable_map_measure (partition_zero_measurable n).aestronglyMeasurable
    (gaussian_disorder_hasLaw β n).aemeasurable).2
  simpa only [Function.comp_def,← gaussianSpinPartition_eq_partition] using
    gaussianSpinPartition_integrable n (β^2/(n:ℝ))

def partitionSizeBias (β : ℝ) (n : ℕ) (J : Disorder n) : ℝ :=
  partition J 0/(∫ J,partition J 0 ∂disorderLaw β n)

lemma partitionSizeBias_pos (β : ℝ) (n : ℕ) (J : Disorder n) :
    0 < partitionSizeBias β n J := by
  unfold partitionSizeBias
  rw [disorder_partition_mean]
  exact div_pos (partition_pos J 0) (gaussianSpinPartition_mean_pos (by positivity))

lemma partitionSizeBias_integrable (β : ℝ) (n : ℕ) :
    Integrable (partitionSizeBias β n) (disorderLaw β n) :=
  (disorder_partition_integrable β n).div_const _

lemma weighted_fixedTimeFailure_integrable (β : ℝ) (n : ℕ) (j A K ε c ρ t : ℝ) :
    Integrable (fun J=> partitionSizeBias β n J*fixedTimeFailure n j A K ε c ρ t J)
      (disorderLaw β n) := by
  apply (partitionSizeBias_integrable β n).mul_bdd
    (measurable_fixedTimeFailure n j A K ε c ρ t).aestronglyMeasurable
  filter_upwards [] with J
  rw [Real.norm_eq_abs,abs_of_nonneg (fixedTimeFailure_nonneg _ _ _ _ _ _ _ _ _)]
  exact fixedTimeFailure_le_one n j A K ε c ρ t J

lemma weighted_fixedTimeFailure_integral_bound (β : ℝ) (n : ℕ) (A K ε c ρ t b : ℝ)
    (hb : 0 ≤ b)
    (hh : (∫⁻ J : Disorder n, ENNReal.ofReal (partitionSizeBias β n J)*
      fixedTimeFailureENN (β^2) A K ε c ρ t J ∂disorderLaw β n) ≤ ENNReal.ofReal b) :
    (∫ J : Disorder n,partitionSizeBias β n J*fixedTimeFailure n (β^2) A K ε c ρ t J
      ∂disorderLaw β n) ≤ b := by
  apply (ENNReal.ofReal_le_ofReal_iff hb).mp
  rw [ofReal_integral_eq_lintegral_ofReal
    (weighted_fixedTimeFailure_integrable β n (β^2) A K ε c ρ t)
    (ae_of_all _ (fun J=>mul_nonneg (partitionSizeBias_pos β n J).le
      (fixedTimeFailure_nonneg _ _ _ _ _ _ _ _ _)))]
  simp_rw [ENNReal.ofReal_mul (partitionSizeBias_pos β n _).le,ofReal_fixedTimeFailure]
  exact hh

theorem quenched_fixed_time_root_stability {β T : ℝ} (hβ : 0<β) (hβ1 : β<1) (hT : 0<T) :
    ∃ A K ε c ρ a : ℝ, 1<A ∧ 2*β<K ∧ β*A<1 ∧
      0<ε ∧ 0<c ∧ 0<ρ ∧ 0<a ∧ ∀ τ : ℕ→ℝ, (∀ n,τ n∈Icc 0 T) →
      Tendsto (fun n=>(disorderLaw β n).real
        {J | exp (-a*(n:ℝ)) < fixedTimeFailure n (β^2) A K ε c ρ (τ n) J}) atTop (𝓝 0) := by
  obtain ⟨A,K,ε,c,ρ,a,hA,hK,hsub,hε,hc,hρ,ha,N,hN,hann⟩ :=
    annealed_fixed_time_root_stability hβ hβ1 hT
  refine ⟨A,K,ε,c,ρ,a/4,hA,hK,hsub,hε,hc,hρ,by positivity,?_⟩
  intro τ hτ
  apply exponential_size_bias_transfer (C:=1) (disorderLaw β) (partitionSizeBias β)
    (fun n=>fixedTimeFailure n (β^2) A K ε c ρ (τ n))
    (fun n J=>(partitionSizeBias_pos β n J).le)
    (fun n J=>fixedTimeFailure_nonneg _ _ _ _ _ _ _ _ _)
    (fun n=>weighted_fixedTimeFailure_integrable _ _ _ _ _ _ _ _ _) ha zero_le_one
  · exact disorder_partition_lower_tail hβ hβ1 (by positivity)
  · filter_upwards [eventually_ge_atTop N] with n hn
    simp only [one_mul]
    exact weighted_fixedTimeFailure_integral_bound β n A K ε c ρ (τ n) _ (exp_pos _).le
      (hann n hn (τ n) (hτ n))
end SKGap.ObservationBridge

end
end

end OAI
