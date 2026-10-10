import OAI.Probability.FreeIsing.Factors.ContinuousRecovery
import OAI.Probability.FreeIsing.Posterior.ArrayPosteriorStationarity

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.ArrayPosteriorStationarity

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem continuous_posterior_array_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    {m : ℝ≥0 → TreeVertex d →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ}
    (hcm : ∀ v, ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      Continuous (fun t => m t v q))
    (hversion : ∀ t v, m t v =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v)
    (g : TreeAut d) :
    ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      (fun v t => m t v (plantedRelabel g q)) =
        relabel g (fun v t => m t v q) := by
  have hcoord (v : TreeVertex d) :
      (fun q t => m t v (plantedRelabel g q)) =ᵐ[
        μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      (fun q t => m t (g.toEquiv.symm v) q) := by
    apply ae_eq_of_continuous_of_evaluation_ae_eq
      ((measurePreserving_plantedRelabel hμ ν g).quasiMeasurePreserving.ae (hcm v))
      (hcm (g.toEquiv.symm v))
    intro t
    exact posterior_version_relabel_ae hμ ν B hmB hversion g t v
  filter_upwards [ae_all_iff.mpr hcoord] with q hq
  exact funext hq

theorem continuous_posterior_field_array_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    {m : ℝ≥0 → TreeVertex d →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ}
    (hcm : ∀ v, ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      Continuous (fun t => m t v q))
    (hversion : ∀ t v, m t v =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v)
    (g : TreeAut d) :
    ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      (fun v t => Real.artanh (m t v (plantedRelabel g q))) =
        relabel g (fun v t => Real.artanh (m t v q)) := by
  filter_upwards [continuous_posterior_array_relabel_ae hμ ν B hmB hcm hversion g]
    with q hq
  funext v t
  exact congrArg Real.artanh (congrFun (congrFun hq v) t)

end Problem367.ArrayPosteriorStationarity

end

end OAI
