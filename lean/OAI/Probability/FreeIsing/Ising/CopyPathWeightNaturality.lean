import OAI.Probability.FreeIsing.Estimates.WeightedOrbitAverage
import OAI.Probability.FreeIsing.Ising.CopyGeodesicCorrelations
import OAI.Probability.FreeIsing.Ising.CopyPathBounds

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyPathBounds
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem edgeLogDifference_eq_cavityLogDifference
    (hbeta : 0 ≤ beta) (t : ℝ≥0) (v w : TreeVertex d) :
    edgeLogDifference hbeta t v w =
      IsingCopySpectral.cavityLogDifference hbeta t v w := rfl

theorem edgeLogDifference_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun q => edgeLogDifference hbeta t v w (copyRelabel g q)) =ᵐ[copies beta μ]
      edgeLogDifference hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w) :=
  IsingCopySpectral.cavityLogDifference_relabel_ae hμ hbeta g t v w

theorem pathLogDifference_relabel_ae {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d) :
    (fun q => pathLogDifference hbeta t s e (copyRelabel g q)) =ᵐ[copies beta μ]
      pathLogDifference hbeta t s
        (fun i => (g.toEquiv.symm (e i).1, g.toEquiv.symm (e i).2)) := by
  have hall := (ae_ball_iff s.finite_toSet.countable).mpr
    (fun i (_hi : i ∈ s) => edgeLogDifference_relabel_ae hμ hbeta g t (e i).1 (e i).2)
  filter_upwards [hall] with q hq
  exact Finset.sum_congr rfl (fun i hi => hq i hi)

theorem pathLogDifference_relabel_eq_ae {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d)
    (hfix : ∀ i ∈ s, g.toEquiv (e i).1 = (e i).1 ∧
      g.toEquiv (e i).2 = (e i).2) :
    (fun q => pathLogDifference hbeta t s e (copyRelabel g q)) =ᵐ[copies beta μ]
      pathLogDifference hbeta t s e := by
  filter_upwards [pathLogDifference_relabel_ae hμ hbeta g t s e] with q hq
  apply hq.trans
  apply Finset.sum_congr rfl
  intro i hi
  have hleft : g.toEquiv.symm (e i).1 = (e i).1 := by
    simpa only [(hfix i hi).1] using g.toEquiv.symm_apply_apply (e i).1
  have hright : g.toEquiv.symm (e i).2 = (e i).2 := by
    simpa only [(hfix i hi).2] using g.toEquiv.symm_apply_apply (e i).2
  simp only [hleft, hright]

theorem pathLogDifference_sq_relabel_eq_ae {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d)
    (hfix : ∀ i ∈ s, g.toEquiv (e i).1 = (e i).1 ∧
      g.toEquiv (e i).2 = (e i).2) :
    (fun q => pathLogDifference hbeta t s e (copyRelabel g q) ^ 2) =ᵐ[copies beta μ]
      (fun q => pathLogDifference hbeta t s e q ^ 2) :=
  (pathLogDifference_relabel_eq_ae hμ hbeta g t s e hfix).fun_comp (fun x : ℝ => x ^ 2)

theorem integral_pathLogDifference_sq_mul_orbit_average
    {ι κ : Type*} [Fintype κ] [Nonempty κ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : κ → TreeAut d) (t : ℝ≥0) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d)
    (hfix : ∀ k i, i ∈ s → (g k).toEquiv (e i).1 = (e i).1 ∧
      (g k).toEquiv (e i).2 = (e i).2)
    (F : IsingConditionalCopyBounds.CopySpace d → ℝ)
    (hF : Integrable (fun q => pathLogDifference hbeta t s e q ^ 2 * F q)
      (copies beta μ)) :
    (∫ q, pathLogDifference hbeta t s e q ^ 2 *
      WeightedOrbitAverage.average (fun k q => F (copyRelabel (g k) q)) q
      ∂copies beta μ) =
      ∫ q, pathLogDifference hbeta t s e q ^ 2 * F q ∂copies beta μ := by
  let T : κ → IsingConditionalCopyBounds.CopySpace d ≃ᵐ
      IsingConditionalCopyBounds.CopySpace d := fun k =>
    (ObservationCopyStationarity.arrayRelabelEquiv (A := WienerSampler.Path) (g k)).prodCongr
      ((ObservationCopyStationarity.arrayRelabelEquiv (A := WienerSampler.Path) (g k)).prodCongr
        (ObservationCopyStationarity.arrayRelabelEquiv (A := WienerSampler.Path) (g k)))
  exact WeightedOrbitAverage.integral_weight_mul_orbit_average T
    (fun k => measurePreserving_copies_relabel hμ (g k))
    (fun q => pathLogDifference hbeta t s e q ^ 2) F
    (fun k => pathLogDifference_sq_relabel_eq_ae hμ hbeta (g k) t s e (hfix k)) hF

end Problem367.IsingCopyPathBounds

end

end OAI
