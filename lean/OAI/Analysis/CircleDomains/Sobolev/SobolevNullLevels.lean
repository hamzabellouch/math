import OAI.Analysis.CircleDomains.Sobolev.SobolevCoareaFiniteLevels

namespace OAI

/-! Coarea forces the actual weak gradient to vanish on the preimage
of any null set of scalar values. In particular, every fixed level has
zero gradient almost everywhere; no regularity of the level is assumed. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem sobolev_gradient_zero_on_null_values
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E)
    {N : Set ℝ} (hN : MeasurableSet N) (hNzero : volume N = 0) :
    ∀ᵐ p ∂volume.restrict (E ∩ v ⁻¹' N), V p = 0 := by
  let A := E ∩ v ⁻¹' N
  have hA : MeasurableSet A := hE.inter (hv.measurable hN)
  have hAb : IsBounded A := hb.subset inter_subset_left
  obtain ⟨hm, he⟩ := hcoarea v hv V hw hLp A hA hAb (fun _ => 1) measurable_const
  have hz : (∫⁻ t, sobolevLevelIntegral A v (fun _ => 1) t) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    have havoid : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ N := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hNzero
    filter_upwards [havoid] with t ht
    have htn : t ∉ N := ht
    have hempty : A ∩ {p | v p = t} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact htn (hp.2 ▸ hp.1.2)
    simp only [sobolevLevelIntegral, hempty, Measure.restrict_empty, lintegral_zero_measure, Pi.zero_apply]
  simp only [one_mul] at he
  have hnorm : AEMeasurable (fun p => ENNReal.ofReal ‖V p‖) (volume.restrict A) :=
    (local_gradient_integrableOn_bounded hLp hAb).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have ha := (lintegral_eq_zero_iff' hnorm).mp (he.symm.trans hz)
  filter_upwards [ha] with p hp
  exact norm_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp hp) (norm_nonneg _))

 theorem sobolev_gradient_zero_on_level
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E) (t : ℝ) :
    ∀ᵐ p ∂volume.restrict (E ∩ {p | v p = t}), V p = 0 := by
  exact sobolev_gradient_zero_on_null_values hcoarea hv hw hLp hE hb
    (measurableSet_singleton t) (measure_singleton t)

end CircleDomainRigidity

end

end OAI
