import OAI.Probability.FreeIsing.Estimates.FreeIsingMeasure
import OAI.Probability.FreeIsing.Factors.Necessity
import OAI.Probability.FreeIsing.Factors.ZeroFactor
import OAI.Probability.FreeIsing.Ising.CriticalSpatialRecovery
import OAI.Probability.FreeIsing.Ising.StrictFactorRecovery

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367
open IsingObservationInnovation IsingObservationFactor IsingCopySmallLogLoss
open ConnectedHull

def ActualRootVarianceIdentity {d : ℕ} (beta : ℝ)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] : Prop :=
  ∀ T : ℝ≥0,
    AbsolutelyContinuousOnInterval
      (fun t : ℝ => siteVariance beta μ (root d) t.toNNReal) 0 (T : ℝ) ∧
    (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (T : ℝ)),
      deriv (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) t =
        ∫ q, IsingCopyEnergy.density beta (root d) t q ∂copies beta μ)

theorem isFactorOfIID_of_sharp_actual_variance_identity
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hsharp : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (hvariance : ActualRootVarianceIdentity beta μ) :
    IsFactorOfIID d (Real.tanh beta) := by
  rcases lt_or_eq_of_le hsharp with hstrict | hcritical
  · exact isFactorOfIID_of_subcritical_actual_variance_identity hμ hb hstrict
      (fun T => (hvariance T).1) (fun T => (hvariance T).2)
  · let c : Fin d := ⟨0, by omega⟩
    let w : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
    have hw : treeAdj (root d) w := Or.inl ⟨c, rfl⟩
    exact IsingCopyResponseRowPaths.isFactorOfIID_of_critical_variance_identity
      hμ hd hb hcritical (root d) w hw (fun T => (hvariance T).1)
      (fun T => ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
        (hvariance T).2)

theorem free_ising_factor_below_threshold_of_actual_variance_identity
    (hvariance : ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 < beta →
      ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1 →
      ActualRootVarianceIdentity beta (freeIsingMeasure d (Real.tanh beta))) :
    ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 ≤ beta →
      Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) →
      IsFactorOfIID d (Real.tanh beta) := by
  intro d beta hd hb hthreshold
  rcases eq_or_lt_of_le hb with hzero | hpos
  · subst beta
    exact free_ising_factor_beta_zero d
  · have hsharp : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1 := by
      simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] using
        (tanh_threshold_iff_branching_sq hd hpos.le).mp hthreshold
    exact isFactorOfIID_of_sharp_actual_variance_identity
      (freeIsingMeasure_hasFreeIsingLaw d (Real.neg_one_lt_tanh beta).le
        (Real.tanh_lt_one beta).le) hd hpos.le hsharp
      (hvariance d beta hd hpos hsharp)

theorem free_ising_factor_iff_threshold_of_actual_variance_identity
    (hvariance : ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 < beta →
      ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1 →
      ActualRootVarianceIdentity beta (freeIsingMeasure d (Real.tanh beta))) :
    ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 ≤ beta →
      (IsFactorOfIID d (Real.tanh beta) ↔
        Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) := by
  intro d beta hd hb
  exact ⟨free_ising_factor_only_if_threshold d beta hd hb,
    free_ising_factor_below_threshold_of_actual_variance_identity
      hvariance d beta hd hb⟩

end Problem367

end

end OAI
