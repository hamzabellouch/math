import OAI.Probability.FreeIsing.Ising.CopyCriticalSpatialBounds
import OAI.Probability.FreeIsing.Ising.CopyNoiseLongBound
import OAI.Probability.FreeIsing.Ising.CriticalCopyEndgame

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationFactor IsingCopySmallLogLoss IsingCriticalSmallLogLoss
open ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_ae_critical_spatial_endpoint_of_noise_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (T : ℝ≥0)
    (u w : TreeVertex d) (huw : treeAdj u w)
    {B E c a q C₀ : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q)
    (hnoise : ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
      ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤
          B * logVariance hb μ u w t *
            ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length)))
    (hderiv : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      deriv (fun r : ℝ => siteVariance beta μ (root d) r.toNNReal) s =
        ∫ z, IsingCopyEnergy.density beta (root d) s z ∂copies beta μ) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      0 < siteVariance beta μ (root d) s.toNNReal →
      CriticalSpatialEndpointBounds
        (deriv (fun r : ℝ => siteVariance beta μ (root d) r.toNNReal) s)
        (∑' n, noiseShellEnergy (μ := μ) hb s.toNNReal n)
        (∑' n, linearShellEnergy (μ := μ) hb s.toNNReal n)
        (∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb s.toNNReal n))
        (logVariance hb μ u w s.toNNReal) (siteVariance beta μ (root d) s.toNNReal)
        M (varianceScale d beta T) (min (Real.sqrt s) 1) := by
  obtain ⟨M, hM, hendpoint⟩ := exists_actual_spatial_endpoint_of_noise_bound
    hμ hd hb hcritical T hB hE hc ha hq hnoise
  refine ⟨M, hM, ?_⟩
  filter_upwards [hderiv, ae_restrict_mem measurableSet_Ioc] with s hs hmem
  intro hV
  have he : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hmem.1.le
  have ht : 0 < s.toNNReal := Real.toNNReal_pos.mpr hmem.1
  have hT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hmem.2
  have h := hendpoint s.toNNReal ht hT u w huw hV
  simpa only [he, ← hs] using h

theorem critical_root_variance_zero_of_noise_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (T : ℝ≥0)
    (u w : TreeVertex d) (huw : treeAdj u w)
    {B E c a q C₀ : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q)
    (hnoise : ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
      ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤
          B * logVariance hb μ u w t *
            ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length)))
    (hAC : AbsolutelyContinuousOnInterval
      (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) 0 (T : ℝ))
    (hderiv : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      deriv (fun r : ℝ => siteVariance beta μ (root d) r.toNNReal) s =
        ∫ z, IsingCopyEnergy.density beta (root d) s z ∂copies beta μ) :
    ∀ t : ℝ≥0, t ≤ T → siteVariance beta μ (root d) t = 0 := by
  obtain ⟨M, hM, hendpoint⟩ := exists_ae_critical_spatial_endpoint_of_noise_bound
    hμ hd hb hcritical T u w huw hB hE hc ha hq hnoise hderiv
  exact IsingCriticalCopyEndgame.siteVariance_eq_zero_of_spatial_endpoint_bounds
    hd hb hcritical hμ T (root d) u w huw hM
    (fun s => ∑' n, noiseShellEnergy (μ := μ) hb s.toNNReal n)
    (fun s => ∑' n, linearShellEnergy (μ := μ) hb s.toNNReal n)
    (fun s => ∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb s.toNNReal n))
    hAC hendpoint

theorem isFactorOfIID_of_critical_variance_and_noise_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (u w : TreeVertex d) (huw : treeAdj u w)
    (hAC : ∀ T : ℝ≥0, AbsolutelyContinuousOnInterval
      (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) 0 (T : ℝ))
    (hderiv : ∀ T : ℝ≥0, ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      deriv (fun r : ℝ => siteVariance beta μ (root d) r.toNNReal) s =
        ∫ z, IsingCopyEnergy.density beta (root d) s z ∂copies beta μ)
    (hnoise : ∀ T : ℝ≥0, ∃ B E c a q C₀ : ℝ,
      0 ≤ B ∧ 0 ≤ E ∧ 0 < c ∧ 0 < a ∧ 1 < q ∧
      ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
      ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤
          B * logVariance hb μ u w t *
            ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length))) :
    IsFactorOfIID d (Real.tanh beta) := by
  apply isFactorOfIID_of_root_field_variance_zero hμ hb (root d)
  intro t
  obtain ⟨B, E, c, a, q, C₀, hB, hE, hc, ha, hq, hbound⟩ := hnoise t
  exact critical_root_variance_zero_of_noise_bound hμ hd hb hcritical t u w huw
    hB hE hc ha hq hbound (hAC t) (hderiv t) t le_rfl

theorem isFactorOfIID_of_critical_variance_identity
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (u w : TreeVertex d) (huw : treeAdj u w)
    (hAC : ∀ T : ℝ≥0, AbsolutelyContinuousOnInterval
      (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) 0 (T : ℝ))
    (hderiv : ∀ T : ℝ≥0, ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      deriv (fun r : ℝ => siteVariance beta μ (root d) r.toNNReal) s =
        ∫ z, IsingCopyEnergy.density beta (root d) s z ∂copies beta μ) :
    IsFactorOfIID d (Real.tanh beta) := by
  apply isFactorOfIID_of_critical_variance_and_noise_bound hμ hd hb hcritical
    u w huw hAC hderiv
  intro T
  obtain ⟨B, E, c, a, q, C₀, hB, hE, hc, ha, hq, _, hnoise⟩ :=
    exists_noise_energy_long_constants hμ hd hb hcritical T
  exact ⟨B, E, c, a, q, C₀, hB, hE, hc, ha, hq, hnoise⟩

end Problem367.IsingCopyResponseRowPaths

end

end OAI
