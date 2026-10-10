import OAI.Probability.FreeIsing.Cavity.Array
import OAI.Probability.FreeIsing.Ising.ConditionalCopyBounds
import OAI.Probability.FreeIsing.Ising.ObservationFactor

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyStationarity

open IsingObservationInnovation IsingObservationFactor

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def copyRelabel (g : TreeAut d) : Paths d × (Paths d × Paths d) →
    Paths d × (Paths d × Paths d) :=
  Prod.map (relabel g) (Prod.map (relabel g) (relabel g))

theorem measurable_copyRelabel (g : TreeAut d) : Measurable (copyRelabel g) :=
  (measurable_relabel g).prodMap ((measurable_relabel g).prodMap (measurable_relabel g))

theorem measurePreserving_copies_relabel
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d) :
    MeasurePreserving (copyRelabel g) (copies beta μ) (copies beta μ) := by
  let T := ObservationCopyStationarity.arrayRelabelEquiv (A := WienerSampler.Path) g
  have hT : MeasurePreserving T
      ((observationLaw μ).map (innovationMap beta))
      ((observationLaw μ).map (innovationMap beta)) := by
    refine ⟨measurable_relabel g, ?_⟩
    rw [map_innovationMap_observationLaw hμ]
    exact Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective
  refine ⟨measurable_copyRelabel g, ?_⟩
  exact conditionalCopies_invariant
    ((observationLaw μ).map (innovationMap beta)) (kernel beta μ) T
    (measurable_relabel g) hT
    (ObservableDisintegration.joint_kernel_invariant (observationLaw μ)
      (measurable_innovationMap beta) (measurable_relabel g)
      (measurePreserving_observationLaw_relabel hμ g) (innovationMap_relabel_ae hμ g))

omit [IsProbabilityMeasure μ] in
theorem posterior_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun x => posterior beta v t (relabel g x)) =ᵐ[observationLaw μ]
      posterior beta (g.toEquiv.symm v) t := by
  have hm (w : TreeVertex d) : Measurable (posterior beta w t) :=
    (measurable_infiniteGibbsSpinMean beta w).comp
      (Measurable.of_eval (fun i => measurable_evaluation i t))
  apply (ae_map_iff measurable_uniformObservation.aemeasurable
    (measurableSet_eq_fun ((hm v).comp (measurable_relabel g))
      (hm (g.toEquiv.symm v)))).mpr
  have hmB (s : ℝ≥0) : Measurable (fun u => WienerSampler.sample u s) :=
    WienerSampler.measurable_sample_eval.comp (measurable_const.prodMk measurable_id)
  have h := ArrayPosteriorStationarity.posterior_version_relabel_ae hμ uniform01
    (fun s u => WienerSampler.sample u s) hmB
    (fun s w => IsingInnovation.posterior_eq_condExp hμ uniform01
      WienerSampler.sample_isBrownianReal.toIsPreBrownianReal hmB s w) g t v
  exact h

omit [IsProbabilityMeasure μ] in
theorem field_array_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d) (t : ℝ≥0) :
    (fun x v => field beta v t (relabel g x)) =ᵐ[observationLaw μ]
      (fun x => relabel g (fun v => field beta v t x)) := by
  filter_upwards [ae_all_iff.mpr (fun v => posterior_relabel_ae hμ g t v)] with x hx
  funext v
  exact congrArg Real.artanh (hx v)

theorem measurePreserving_observations :
    MeasurePreserving (fun q : Paths d × (Paths d × Paths d) => q.2.1)
      (copies beta μ) (observationLaw μ) ∧
    MeasurePreserving (fun q : Paths d × (Paths d × Paths d) => q.2.2)
      (copies beta μ) (observationLaw μ) := by
  apply IsingConditionalCopyBounds.measurePreserving_observation_copies
  exact ObservableDisintegration.compProd_kernel (observationLaw μ)
    (measurable_innovationMap beta)

def sitePair (beta : ℝ) (t : ℝ≥0) (q : Paths d × (Paths d × Paths d)) :
    CavityArray.SitePair d :=
  (fun v => field beta v t q.2.1, fun v => field beta v t q.2.2)

theorem measurable_sitePair (beta : ℝ) (t : ℝ≥0) :
    Measurable (sitePair (d := d) beta t) := by
  have hm (v : TreeVertex d) : Measurable (field beta v t) := by
    have hp : Measurable (posterior beta v t) :=
      (measurable_infiniteGibbsSpinMean beta v).comp
        (Measurable.of_eval (fun i => measurable_evaluation i t))
    unfold field Real.artanh
    exact ((measurable_const.add hp).div (measurable_const.sub hp)).sqrt.log
  exact (Measurable.of_eval (fun v => (hm v).comp (measurable_fst.comp measurable_snd))).prodMk
    (Measurable.of_eval (fun v => (hm v).comp (measurable_snd.comp measurable_snd)))

theorem measurePreserving_sitePair_relabel
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (g : TreeAut d) :
    MeasurePreserving (CavityArray.pairRelabel g)
      ((copies beta μ).map (sitePair beta t))
      ((copies beta μ).map (sitePair beta t)) := by
  refine ⟨CavityArray.measurable_pairRelabel g, ?_⟩
  apply FactorTransport.map_invariant_of_ae_equivariant
    (measurePreserving_copies_relabel hμ g) (CavityArray.measurable_pairRelabel g)
    (measurable_sitePair beta t)
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  filter_upwards [hl.quasiMeasurePreserving.ae (field_array_relabel_ae hμ g t),
    hr.quasiMeasurePreserving.ae (field_array_relabel_ae hμ g t)] with q hq hq'
  exact Prod.ext hq hq'

theorem fieldDifference_identDistrib
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (u v : TreeVertex d) :
    IdentDistrib (IsingConditionalCopyBounds.fieldDifference beta u t)
      (IsingConditionalCopyBounds.fieldDifference beta v t) (copies beta μ) (copies beta μ) := by
  have hm (w : TreeVertex d) : Measurable (fun p : CavityArray.SitePair d => p.1 w - p.2 w) :=
    ((measurable_pi_apply w).comp measurable_fst).sub
      ((measurable_pi_apply w).comp measurable_snd)
  have h := CavityArray.site_sub_identDistrib
    (measurePreserving_sitePair_relabel hμ t) u v
  refine ⟨((hm u).comp (measurable_sitePair beta t)).aemeasurable,
    ((hm v).comp (measurable_sitePair beta t)).aemeasurable, ?_⟩
  change (copies beta μ).map ((fun p : CavityArray.SitePair d => p.1 u - p.2 u) ∘
    sitePair beta t) = (copies beta μ).map
      ((fun p : CavityArray.SitePair d => p.1 v - p.2 v) ∘ sitePair beta t)
  rw [← Measure.map_map (hm u) (measurable_sitePair beta t),
    ← Measure.map_map (hm v) (measurable_sitePair beta t)]
  exact h.map_eq

theorem integral_fieldDifference_sq_eq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (u v : TreeVertex d) :
    (∫ q, (IsingConditionalCopyBounds.fieldDifference beta u t q) ^ 2 ∂copies beta μ) =
      ∫ q, (IsingConditionalCopyBounds.fieldDifference beta v t q) ^ 2 ∂copies beta μ :=
  (fieldDifference_identDistrib hμ t u v).sq.integral_eq

end Problem367.IsingCopyStationarity

end

end OAI
