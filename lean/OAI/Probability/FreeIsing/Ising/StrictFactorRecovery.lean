import OAI.Probability.FreeIsing.Ising.CopySmallLogLoss
import OAI.Probability.FreeIsing.Ising.CopySpatialEndpoints
import OAI.Probability.FreeIsing.Ising.CopyStrictComparison

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation IsingCopyResponseRowPaths IsingCopySmallLogLoss
open ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem siteVariance_eq_zero_of_subcritical_actual_variance_identity
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1) (T : ℝ≥0)
    (hAC : AbsolutelyContinuousOnInterval
      (fun t : ℝ => siteVariance beta μ (root d) t.toNNReal) 0 (T : ℝ))
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (T : ℝ)),
      deriv (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) t =
        ∫ q, IsingCopyEnergy.density beta (root d) t q ∂copies beta μ) :
    ∀ t : ℝ≥0, t ≤ T → siteVariance beta μ (root d) t = 0 := by
  have hrestricted := (ae_restrict_iff' measurableSet_Icc).mp hderiv
  have hpath : ∀ᵐ t : ℝ, t ∈ Icc 0 (T : ℝ) →
      deriv (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) t =
        ∫ q, DiscrepancyEnergy.density
          (fun v q => row beta t.toNNReal v q.2.1)
          (fun v q => row beta t.toNNReal v q.2.2)
          (IsingConditionalCopyBounds.fieldDifference beta (root d) t.toNNReal)
          (fun q => Real.tanh (field beta (root d) t.toNNReal q.2.1))
          (fun q => Real.tanh (field beta (root d) t.toNNReal q.2.2)) q
            ∂copies beta μ := by
    filter_upwards [hrestricted] with t ht hmem
    rw [ht hmem]
    have he := actual_density_eq_path_density_ae hμ hb t.toNNReal
    rw [Real.coe_toNNReal t hmem.1] at he
    exact integral_congr_ae he
  have hzero := root_variance_eq_zero_of_subcritical_variance_identity
    hμ hb hstrict (T : ℝ) hAC hpath
  intro t ht
  simpa only [Real.toNNReal_coe, siteVariance] using
    hzero (t : ℝ) ⟨t.coe_nonneg, ht⟩

theorem isFactorOfIID_of_subcritical_actual_variance_identity
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (hAC : ∀ T : ℝ≥0, AbsolutelyContinuousOnInterval
      (fun t : ℝ => siteVariance beta μ (root d) t.toNNReal) 0 (T : ℝ))
    (hderiv : ∀ T : ℝ≥0,
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (T : ℝ)),
        deriv (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) t =
          ∫ q, IsingCopyEnergy.density beta (root d) t q ∂copies beta μ) :
    IsFactorOfIID d (Real.tanh beta) := by
  apply isFactorOfIID_of_root_field_variance_zero hμ hb (root d)
  intro t
  exact siteVariance_eq_zero_of_subcritical_actual_variance_identity
    hμ hb hstrict t (hAC t) (hderiv t) t le_rfl

theorem isFactorOfIID_of_lt_threshold_actual_variance_identity
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hstrict : Real.tanh beta < 1 / Real.sqrt ((d : ℝ) - 1))
    (hAC : ∀ T : ℝ≥0, AbsolutelyContinuousOnInterval
      (fun t : ℝ => siteVariance beta μ (root d) t.toNNReal) 0 (T : ℝ))
    (hderiv : ∀ T : ℝ≥0,
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (T : ℝ)),
        deriv (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) t =
          ∫ q, IsingCopyEnergy.density beta (root d) t q ∂copies beta μ) :
    IsFactorOfIID d (Real.tanh beta) := by
  apply isFactorOfIID_of_subcritical_actual_variance_identity hμ hb
    (hAC := hAC) (hderiv := hderiv)
  have h := (threshold_lt_iff_branching_sq_lt hd
    (tanh_nonneg_of_beta_nonneg hb)).mp hstrict
  simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] using h

end Problem367.IsingObservationFactor

end

end OAI
