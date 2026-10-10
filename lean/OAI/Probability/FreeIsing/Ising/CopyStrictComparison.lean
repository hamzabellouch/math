import OAI.Probability.FreeIsing.Energy.SubcriticalResponseComparison
import OAI.Probability.FreeIsing.Ising.CopyResponseRowPaths
import OAI.Probability.FreeIsing.Ising.ObservationComparison

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyStationarity ResponseRows

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem integral_density_le_subcritical
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1) (t : ℝ≥0) :
    let U := IsingConditionalCopyBounds.fieldDifference beta (ConnectedHull.root d) t
    let D := DiscrepancyEnergy.density (fun v q => row beta t v q.2.1)
      (fun v q => row beta t v q.2.2) U
      (fun q => Real.tanh (field beta (ConnectedHull.root d) t q.2.1))
      (fun q => Real.tanh (field beta (ConnectedHull.root d) t q.2.2))
    Integrable D (copies beta μ) ∧
      (∫ q, D q ∂copies beta μ) ≤
        subcriticalPathConstant d (Real.tanh beta)
          (2 * cavityLogVarianceCoefficient (Real.tanh beta)) *
            (∫ q, U q ^ 2 ∂copies beta μ) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  let X := fun v i (q : IsingConditionalCopyBounds.CopySpace d) => pathCavity hb t v i q.2.1
  let Y := fun v i (q : IsingConditionalCopyBounds.CopySpace d) => pathCavity hb t v i q.2.2
  let H := fun q : IsingConditionalCopyBounds.CopySpace d => field beta (ConnectedHull.root d) t q.2.1
  let H' := fun q : IsingConditionalCopyBounds.CopySpace d => field beta (ConnectedHull.root d) t q.2.2
  have hpath (v : TreeVertex d) (i : ℕ) : MemLp (pathCavity hb t v i) 2 (observationLaw μ) :=
    memLp_cavityObservable hμ hb t _ _
  have hXm (v : TreeVertex d) (i : ℕ) : Measurable (X v i) :=
    (measurable_cavityObservable hb t _ _).comp hl.measurable
  have hYm (v : TreeVertex d) (i : ℕ) : Measurable (Y v i) :=
    (measurable_cavityObservable hb t _ _).comp hr.measurable
  have hInt (v : TreeVertex d) (i : ℕ) :
      Integrable (fun q => (X v i q - Y v i q) ^ 2) (copies beta μ) :=
    ((hpath v i).comp_measurePreserving hl |>.sub
      ((hpath v i).comp_measurePreserving hr)).integrable_sq
  have hU : MemLp (fun q => H q - H' q) 2 (copies beta μ) :=
    ((memLp_field_at hμ hb t _).comp_measurePreserving hl).sub
      ((memLp_field_at hμ hb t _).comp_measurePreserving hr)
  have hlog (v : TreeVertex d) (i : ℕ) :
      (∫ q, (Real.log (responseAttenuation (Real.tanh beta) (X v i q)) -
        Real.log (responseAttenuation (Real.tanh beta) (Y v i q))) ^ 2 ∂copies beta μ) ≤
      cavityLogVarianceCoefficient (Real.tanh beta) *
        (∫ q, (H q - H' q) ^ 2 ∂copies beta μ) := by
    have h := norm_cavityLogDifference_sq_le hμ hb t (ConnectedHull.root d)
      (ConnectedHull.takeVertex v (i + 1)) (ConnectedHull.takeVertex v i)
    rw [norm_observableDifference_sq] at h
    exact h
  have hmain := ResponseRows.integral_tree_density_le_subcritical
    (fun v : TreeVertex d => Finset.range v.1.length) (fun v => Finset.card_range _)
    (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_sq_lt_one beta).le hstrict
    (cavityLogVarianceCoefficient_nonneg (Real.tanh beta))
    (fun v i _ => hXm v i) (fun v i _ => hYm v i) (fun v i _ => hInt v i)
    ((measurable_field_at beta t _).comp hl.measurable)
    ((measurable_field_at beta t _).comp hr.measurable) hU (fun v i _ => hlog v i)
  have hd : DiscrepancyEnergy.density (fun v q => row beta t v q.2.1)
      (fun v q => row beta t v q.2.2) (fun q => H q - H' q)
      (fun q => Real.tanh (H q)) (fun q => Real.tanh (H' q)) =ᵐ[copies beta μ]
      DiscrepancyEnergy.density
        (coefficient (Real.tanh beta) (fun w : TreeVertex d => Real.tanh beta ^ w.1.length)
          (fun w => Finset.range w.1.length) X)
        (coefficient (Real.tanh beta) (fun w : TreeVertex d => Real.tanh beta ^ w.1.length)
          (fun w => Finset.range w.1.length) Y)
        (fun q => H q - H' q) (fun q => Real.tanh (H q)) (fun q => Real.tanh (H' q)) := by
    filter_upwards [rows_eq_products_ae hμ hb t] with q hq
    simp only [DiscrepancyEnergy.density, X, Y, (hq _).1, (hq _).2]
  exact ⟨hmain.1.congr hd.symm, (integral_congr_ae hd).trans_le hmain.2⟩

theorem root_variance_eq_zero_of_subcritical_variance_identity
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1) (T : ℝ)
    (hAC : AbsolutelyContinuousOnInterval
      (fun t : ℝ => ∫ q, (IsingConditionalCopyBounds.fieldDifference beta
        (ConnectedHull.root d) t.toNNReal q) ^ 2 ∂copies beta μ) 0 T)
    (hderiv : ∀ᵐ t : ℝ, t ∈ Icc 0 T →
      deriv (fun s : ℝ => ∫ q, (IsingConditionalCopyBounds.fieldDifference beta
        (ConnectedHull.root d) s.toNNReal q) ^ 2 ∂copies beta μ) t =
      ∫ q, DiscrepancyEnergy.density (fun v q => row beta t.toNNReal v q.2.1)
        (fun v q => row beta t.toNNReal v q.2.2)
        (IsingConditionalCopyBounds.fieldDifference beta (ConnectedHull.root d) t.toNNReal)
        (fun q => Real.tanh (field beta (ConnectedHull.root d) t.toNNReal q.2.1))
        (fun q => Real.tanh (field beta (ConnectedHull.root d) t.toNNReal q.2.2)) q
          ∂copies beta μ) :
    ∀ t ∈ Icc 0 T, (∫ q, (IsingConditionalCopyBounds.fieldDifference beta
      (ConnectedHull.root d) t.toNNReal q) ^ 2 ∂copies beta μ) = 0 := by
  apply eq_zero_of_ae_deriv_le_mul_self
    (C := subcriticalPathConstant d (Real.tanh beta)
      (2 * cavityLogVarianceCoefficient (Real.tanh beta))) hAC
  · simpa only [Real.toNNReal_zero, IsingConditionalCopyBounds.fieldDifference, field] using
      (initial_field_difference_energy (beta := beta) (μ := μ) (ConnectedHull.root d))
  · exact fun t _ => integral_nonneg (fun q => sq_nonneg _)
  · filter_upwards [hderiv] with t ht hmem
    rw [ht hmem]
    exact (integral_density_le_subcritical hμ hb hstrict t.toNNReal).2

end Problem367.IsingCopyResponseRowPaths

end

end OAI
