import Mathlib
import OAI.Probability.SKBarriers.Interpolation.RestrictedReplicas

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem restrictedLogPartition_subGaussian {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (β : ℝ) {S : Finset (ReplicaConfig n d)} (hS : S.Nonempty) :
    HasSubgaussianMGF (fun J : Disorder n => restrictedLogPartition β S J-
      ∫ K, restrictedLogPartition β S K ∂disorderLaw n)
      (logPartitionProxy (β*(d:ℝ)) n) (disorderLaw n) := by
  let inst : SmoothFamily.Model n := restrictedModel hd S hS
  have H := @SmoothFamily.logPartition_subGaussian n inst hn (β*(d:ℝ))
  change HasSubgaussianMGF (fun J => restrictedLogPartition ((β*(d:ℝ))/(d:ℝ)) S J-
    ∫ K, restrictedLogPartition ((β*(d:ℝ))/(d:ℝ)) S K ∂disorderLaw n)
    (logPartitionProxy (β*(d:ℝ)) n) (disorderLaw n) at H
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simpa only [mul_div_cancel_right₀ _ hd'] using H

theorem restrictedLogPartition_integrable {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (β : ℝ) {S : Finset (ReplicaConfig n d)} (hS : S.Nonempty) :
    Integrable (restrictedLogPartition β S) (disorderLaw n) := by
  let inst : SmoothFamily.Model n := restrictedModel hd S hS
  have H := @SmoothFamily.logPartition_integrable n inst hn (β*(d:ℝ))
  change Integrable (restrictedLogPartition ((β*(d:ℝ))/(d:ℝ)) S) (disorderLaw n) at H
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simpa only [mul_div_cancel_right₀ _ hd'] using H

theorem restrictedLogPartition_upper_tail {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (β u : ℝ) {S : Finset (ReplicaConfig n d)} (hS : S.Nonempty) (hu : 0 ≤ u) :
    (disorderLaw n).real {J | u ≤ restrictedLogPartition β S J-
      ∫ K, restrictedLogPartition β S K ∂disorderLaw n} ≤
      Real.exp (-u^2/(2*(logPartitionProxy (β*(d:ℝ)) n:ℝ))) :=
  (restrictedLogPartition_subGaussian hn hd β hS).measure_ge_le hu

def replicaGibbsMass {n d : ℕ} (β : ℝ) (J : Disorder n) (S : Finset (ReplicaConfig n d)) : ℝ :=
  ∑ s ∈ S, ∏ a, gibbs β J (s a)

theorem replicaGibbsMass_nonneg {n d : ℕ} (β : ℝ) (J : Disorder n) (S : Finset (ReplicaConfig n d)) :
    0 ≤ replicaGibbsMass β J S :=
  Finset.sum_nonneg (fun s _ => Finset.prod_nonneg (fun a _ => (gibbs_pos β J (s a)).le))

theorem replicaGibbsMass_le_one {n d : ℕ} (β : ℝ) (J : Disorder n) (S : Finset (ReplicaConfig n d)) :
    replicaGibbsMass β J S ≤ 1 := by
  have H : replicaGibbsMass β J S ≤ ∑ s : ReplicaConfig n d, ∏ a, gibbs β J (s a) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun s _ _ => Finset.prod_nonneg (fun a _ => (gibbs_pos β J (s a)).le))
  rw [← Fintype.prod_sum] at H
  simpa only [gibbs_sum,Finset.prod_const_one] using H

theorem replicaGibbsMass_eq_ratio {n d : ℕ} (β : ℝ) (J : Disorder n) (S : Finset (ReplicaConfig n d)) :
    replicaGibbsMass β J S = restrictedPartition β S J/(partition β J)^d := by
  unfold replicaGibbsMass restrictedPartition
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  simp only [gibbs,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  rw [replicaEnergy,Finset.mul_sum,Real.exp_sum]

theorem replicaGibbsMass_eq_exp {n d : ℕ} (β : ℝ) (J : Disorder n) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) : replicaGibbsMass β J S =
      Real.exp (restrictedLogPartition β S J-(d:ℝ)*logPartition β J) := by
  rw [replicaGibbsMass_eq_ratio,Real.exp_sub,Real.exp_nat_mul,restrictedLogPartition,logPartition,
    Real.exp_log (restrictedPartition_pos β hS J),Real.exp_log (partition_pos β J)]

theorem continuous_replicaGibbsMass {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) :
    Continuous (fun J : Disorder n => replicaGibbsMass β J S) := by
  apply continuous_finsetSum
  intro s _
  exact continuous_finsetProd _ (fun a _ => continuous_gibbs β (s a))

theorem replicaGibbsMass_integrable {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) :
    Integrable (fun J : Disorder n => replicaGibbsMass β J S) (disorderLaw n) := by
  apply (integrable_const (1:ℝ)).mono' (continuous_replicaGibbsMass β S).aestronglyMeasurable
  filter_upwards [] with J
  simpa only [Real.norm_eq_abs,abs_of_nonneg (replicaGibbsMass_nonneg β J S)] using
    replicaGibbsMass_le_one β J S

end SK.Analytic

end
end

end

end OAI
