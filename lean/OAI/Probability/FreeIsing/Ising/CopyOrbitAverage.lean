import OAI.Probability.FreeIsing.Ising.CopyCavityBounds
import OAI.Probability.FreeIsing.Trees.OrbitAverage

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.IsingCopyOrbitAverage

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open TreeOrbitAverage

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def copyAction (g : TreeAut d) : CopySpace d ≃ᵐ CopySpace d :=
  let e := ObservationCopyStationarity.arrayRelabelEquiv (A := WienerSampler.Path) g.symm
  e.prodCongr (e.prodCongr e)

theorem measurePreserving_copyAction
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d) :
    MeasurePreserving (copyAction g) (copies beta μ) (copies beta μ) :=
  IsingCopyStationarity.measurePreserving_copies_relabel hμ g.symm

theorem fieldDifference_copyAction_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun q => fieldDifference beta v t (copyAction g q)) =ᵐ[copies beta μ]
      fieldDifference beta (g.toEquiv v) t := by
  obtain ⟨hl, hr⟩ := IsingCopyStationarity.measurePreserving_observations
    (beta := beta) (μ := μ)
  filter_upwards [hl.quasiMeasurePreserving.ae
      (IsingCopyStationarity.field_array_relabel_ae hμ g.symm t),
    hr.quasiMeasurePreserving.ae
      (IsingCopyStationarity.field_array_relabel_ae hμ g.symm t)] with q hq hq'
  change field beta v t (relabel g.symm q.2.1) -
      field beta v t (relabel g.symm q.2.2) =
    field beta (g.toEquiv v) t q.2.1 - field beta (g.toEquiv v) t q.2.2
  rw [congrFun hq v, congrFun hq' v]
  rfl

theorem fieldDifference_sq_invariant
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0)
    {stem : List (Fin d)} (o : TreeVertex d) (ho : o.1.length ≤ stem.length)
    (g : TreeAut d) (hg : FixesStemBall stem g) :
    ∀ᵐ q ∂copies beta μ,
      (fieldDifference beta o t (copyAction g q)) ^ 2 =
        (fieldDifference beta o t q) ^ 2 := by
  filter_upwards [fieldDifference_copyAction_ae hμ g t o] with q hq
  rw [hq, hg o ho]

theorem integral_fieldDifference_sq_mul_extension_average
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {stem : List (Fin d)} {n : ℕ}
    (o : TreeVertex d) (ho : o.1.length ≤ stem.length) (s₀ : Extension stem n)
    (F : TreeVertex d → CopySpace d → ℝ)
    (hmF : ∀ v, Measurable (F v))
    (hF01 : ∀ v q, 0 ≤ F v q ∧ F v q ≤ 1)
    (hcov : ∀ g, FixesStemBall stem g → ∀ v, ∀ᵐ q ∂copies beta μ,
      F v (copyAction g q) = F (g.toEquiv v) q) :
    (∫ q, (fieldDifference beta o t q) ^ 2 * F (endpoint s₀) q ∂copies beta μ) =
      ∫ q, (fieldDifference beta o t q) ^ 2 * WeightedOrbitAverage.average
        (fun s : Extension stem n => F (endpoint s)) q ∂copies beta μ := by
  apply TreeOrbitAverage.integral_weight_mul_extension_average s₀ copyAction
    (measurePreserving_copyAction hμ) (fun q => (fieldDifference beta o t q) ^ 2) F
    (fieldDifference_sq_invariant hμ t o ho) hcov
  apply (IsingCopyStationarity.integrable_fieldDifference_sq hμ hbeta t o).mul_bdd
    (hmF (endpoint s₀)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun q => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF01 (endpoint s₀) q).1]
      using (hF01 (endpoint s₀) q).2)

end Problem367.IsingCopyOrbitAverage

end

end OAI
