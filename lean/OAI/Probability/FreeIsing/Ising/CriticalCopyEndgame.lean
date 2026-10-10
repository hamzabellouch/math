import OAI.Probability.FreeIsing.Critical.GlobalEndgame
import OAI.Probability.FreeIsing.Ising.CriticalSmallLogLoss

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingCriticalCopyEndgame

open IsingObservationFactor IsingCopySmallLogLoss IsingCriticalSmallLogLoss

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem siteVariance_eq_zero_of_spatial_endpoint_bounds
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (T : ℝ≥0) (o v w : TreeVertex d) (hvw : treeAdj v w)
    {C : ℝ} (hC : 1 ≤ C) (Q L Z : ℝ → ℝ)
    (hAC : AbsolutelyContinuousOnInterval
      (fun s : ℝ => siteVariance beta μ o s.toNNReal) 0 (T : ℝ))
    (hendpoint : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      0 < siteVariance beta μ o s.toNNReal →
      CriticalSpatialEndpointBounds
        (deriv (fun r : ℝ => siteVariance beta μ o r.toNNReal) s)
        (Q s) (L s) (Z s) (logVariance hbeta μ v w s.toNNReal)
        (siteVariance beta μ o s.toNNReal) C (varianceScale d beta T)
        (min (Real.sqrt s) 1)) :
    ∀ t : ℝ≥0, t ≤ T → siteVariance beta μ o t = 0 := by
  obtain ⟨c, δ, hc, hδ, hδ1, hsmall⟩ :=
    exists_critical_small_log_bounds hd hbeta hcritical
  have hupper (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (T : ℝ)) :
      siteVariance beta μ o s.toNNReal ≤ varianceScale d beta T :=
    siteVariance_le_varianceScale hμ hbeta o (Real.toNNReal_le_iff_le_coe.mpr hs.2)
  have hzero := eq_zero_of_ae_critical_spatial_endpoint_bounds
    (V := fun s : ℝ => siteVariance beta μ o s.toNNReal)
    (S := fun s : ℝ => logVariance hbeta μ v w s.toNNReal)
    (Q := Q) (L := L) (Z := Z)
    (cutoff := δ) (C := C) (H := varianceScale d beta T)
    (A := cavityLogVarianceCoefficient (Real.tanh beta))
    (B := cavityLogTailCoefficient (Real.tanh beta)
      (2 * (T : ℝ) + 2 * (d : ℝ) * beta))
    (c := c) (K := varianceScale d beta T)
    T.coe_nonneg hδ hδ1 hC (one_le_varianceScale d beta T)
    (cavityLogVarianceCoefficient_nonneg _) (cavityLogTailCoefficient_nonneg _ _)
    hc (one_le_varianceScale d beta T) hAC
    (by simpa only [Real.toNNReal_zero] using (siteVariance_zero (beta := beta) (μ := μ) o))
    (fun s _ => siteVariance_nonneg o s.toNNReal) hupper hupper hendpoint ?_
  · intro t htT
    simpa only [Real.toNNReal_coe] using hzero (t : ℝ) ⟨t.coe_nonneg, htT⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro hsδ _
    have he : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs.1.le
    have hst : 0 < (s.toNNReal : ℝ) := by rw [he]; exact hs.1
    have hsd : (s.toNNReal : ℝ) ≤ δ := by rw [he]; exact hsδ
    simpa only [he] using
      (hsmall μ hμ T o v w hvw s.toNNReal hst
        (Real.toNNReal_le_iff_le_coe.mpr hs.2) hsd).1

theorem isFactorOfIID_of_spatial_endpoint_bounds
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (o v w : TreeVertex d) (hvw : treeAdj v w)
    (hAC : ∀ T : ℝ≥0, AbsolutelyContinuousOnInterval
      (fun s : ℝ => siteVariance beta μ o s.toNNReal) 0 (T : ℝ))
    (hendpoint : ∀ T : ℝ≥0, ∃ C : ℝ, 1 ≤ C ∧ ∃ Q L Z : ℝ → ℝ,
      ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      0 < siteVariance beta μ o s.toNNReal →
      CriticalSpatialEndpointBounds
        (deriv (fun r : ℝ => siteVariance beta μ o r.toNNReal) s)
        (Q s) (L s) (Z s) (logVariance hbeta μ v w s.toNNReal)
        (siteVariance beta μ o s.toNNReal) C (varianceScale d beta T)
        (min (Real.sqrt s) 1)) :
    IsFactorOfIID d (Real.tanh beta) := by
  apply isFactorOfIID_of_root_field_variance_zero hμ hbeta o
  intro t
  obtain ⟨C, hC, Q, L, Z, hbounds⟩ := hendpoint t
  exact siteVariance_eq_zero_of_spatial_endpoint_bounds hd hbeta hcritical hμ
    t o v w hvw hC Q L Z (hAC t) hbounds t le_rfl

end Problem367.IsingCriticalCopyEndgame

end

end OAI
