import OAI.Probability.FreeIsing.Ising.CopyProductPathBound
import OAI.Probability.FreeIsing.Trees.CoupledPathDrift

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity
open IsingConditionalCopyBounds ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

private theorem memLp_siteDifference
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (o : TreeVertex d) :
    MemLp (fieldDifference beta o t) 2 (copies beta μ) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  exact ((memLp_field_at hμ hbeta t o).comp_measurePreserving hl).sub
    ((memLp_field_at hμ hbeta t o).comp_measurePreserving hr)

theorem exists_cavityProduct_path_drift_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w →
      ∀ (g : TreeAut d) (v : TreeVertex d) (reverse : Bool) (o : TreeVertex d),
      Integrable (fun q => |fieldDifference beta o t q| *
        |(pathCavityProduct hbeta t g v reverse q.2.1) ^ 2 -
          (pathCavityProduct hbeta t g v reverse q.2.2) ^ 2|) (copies beta μ) ∧
      (∫ q, |fieldDifference beta o t q| *
        |(pathCavityProduct hbeta t g v reverse q.2.1) ^ 2 -
          (pathCavityProduct hbeta t g v reverse q.2.2) ^ 2| ∂copies beta μ) ≤
        2 * Real.sqrt (2 * ∫ q, (fieldDifference beta o t q) ^ 2 ∂copies beta μ) *
          Real.sqrt (C * v.1.length *
            ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ) := by
  obtain ⟨C, hC, hpath⟩ := exists_cavityProduct_path_variance_bound hμ hd hbeta hthreshold
  refine ⟨C, hC, ?_⟩
  intro t u w huw g v reverse o
  have hθ : (Real.tanh beta) ^ 2 ≤ 1 := by
    have h0 := tanh_nonneg_of_beta_nonneg hbeta
    have h1 := Real.tanh_lt_one beta
    nlinarith
  let a := fun i : Fin v.1.length =>
    g.toEquiv (takeVertex v (if reverse then i.1 + 1 else i.1))
  let b := fun i : Fin v.1.length =>
    g.toEquiv (takeVertex v (if reverse then i.1 else i.1 + 1))
  have hraw := integral_abs_mul_prod_responseAttenuation_sq_sub_sq_le Finset.univ hθ
    (fun i _ => (measurable_cavityObservable hbeta t (a i) (b i)).comp
      (measurable_fst.comp measurable_snd))
    (fun i _ => (measurable_cavityObservable hbeta t (a i) (b i)).comp
      (measurable_snd.comp measurable_snd))
    (fun i _ => (memLp_cavityObservable_difference hμ hbeta t (a i) (b i)).integrable_sq)
    (memLp_siteDifference hμ hbeta t o)
  refine ⟨hraw.1, hraw.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (hpath t u w huw g v reverse).2) (by positivity)

end Problem367.IsingCopySpectral

end

end OAI
