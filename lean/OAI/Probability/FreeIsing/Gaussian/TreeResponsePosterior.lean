import OAI.Probability.FreeIsing.Gaussian.TreeResponse
import OAI.Probability.FreeIsing.Posterior.InfinitePosteriorField

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem GibbsLeaf.energy_eq_fieldEnergy {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (h : TreeVertex d → ℝ) (eta : D → IsingSpin) :
    GibbsLeaf.energy beta h D (extendFiniteSpin D eta) =
      FinitePosterior.fieldEnergy (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) v => spinSign (eta v)) (D.restrict h) eta := by
  classical
  have hsum : (∑ x ∈ D, h x * spinSign (extendFiniteSpin D eta x)) =
      ∑ x : D, h x * spinSign (eta x) := by
    rw [← Finset.sum_coe_sort D (fun x => h x * spinSign (extendFiniteSpin D eta x))]
    apply Finset.sum_congr rfl
    intro x _
    rw [extendFiniteSpin_apply D eta x]
  unfold GibbsLeaf.energy FinitePosterior.fieldEnergy finiteIsingEnergy
  rw [hsum]
  exact add_comm _ _

theorem GibbsLeaf.expectation_eq_fieldMean {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (h : TreeVertex d → ℝ)
    (q : (D → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)) q =
      FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) v => spinSign (eta v)) q (D.restrict h) := by
  simp only [LeafGibbs.expectation, FinitePosterior.fieldMean,
    GibbsLeaf.energy_eq_fieldEnergy]

theorem HasFreeIsingLaw.finiteObservation_condExp_treeMean {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0) (v : D) :
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
      fun p => spinSign (p.1 v.1) |
      MeasurableSpace.comap (finiteObservation D t) inferInstance] =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => TreePathResponse.mean beta (PlantedSymmetry.observation t p) D v.1 := by
  have heq := hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta v))
  filter_upwards [heq] with p hp
  change (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
    fun p => spinSign (p.1 v.1) |
    MeasurableSpace.comap (finiteObservation D t) inferInstance] p = _ at hp
  rw [hp]
  simp only [TreePathResponse.mean, extendFiniteSpin_apply D _ v,
    GibbsLeaf.expectation_eq_fieldMean]
  rfl

theorem HasFreeIsingLaw.finiteObservation_normalizedResponse {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0) (u v : D) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    let m := MeasurableSpace.comap (finiteObservation D t) inferInstance
    (fun p => ((P[fun q => spinSign (q.1 u.1) * spinSign (q.1 v.1) | m]) p -
      (P[fun q => spinSign (q.1 u.1) | m]) p *
      (P[fun q => spinSign (q.1 v.1) | m]) p) /
      (1 - (P[fun q => spinSign (q.1 u.1) | m]) p ^ 2)) =ᵐ[P]
      fun p => GaussianTreeResponse.response beta D u.1 v.1
        (PlantedSymmetry.observation t p) := by
  dsimp only
  have hpair := hμ.finiteObservation_condExp D hD t
    (fun eta => spinSign (eta u) * spinSign (eta v))
  filter_upwards [hpair, hμ.finiteObservation_condExp_treeMean D hD t u,
    hμ.finiteObservation_condExp_treeMean D hD t v] with p hp hu hv
  change (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
    fun q => spinSign (q.1 u.1) * spinSign (q.1 v.1) |
    MeasurableSpace.comap (finiteObservation D t) inferInstance] p = _ at hp
  rw [hp, hu, hv]
  unfold GaussianTreeResponse.response TreePathResponse.response TreePathResponse.covariance
    LeafGibbs.covariance
  simp only [extendFiniteSpin_apply D _ u, extendFiniteSpin_apply D _ v,
    GibbsLeaf.expectation_eq_fieldMean, TreePathResponse.mean]
  rfl

end Problem367

end

end OAI
