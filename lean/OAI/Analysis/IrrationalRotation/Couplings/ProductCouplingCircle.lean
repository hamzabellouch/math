import OAI.Analysis.IrrationalRotation.Model.ProductCouplingCircle
import OAI.Analysis.IrrationalRotation.Couplings.ProductCoupling
import OAI.Analysis.IrrationalRotation.Rotation.CircleRepresentative
import OAI.Analysis.IrrationalRotation.Analysis.DensityTransport

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling

lemma baseLaw_eq_restrict : baseLaw = volume.restrict (Ico (0 : ℝ) 1) := by
  simp [baseLaw, CouplingMixture.intervalLaw, ProbabilityTheory.cond, Real.volume_Ico]

lemma circleEndpoint_measurable : Measurable circleEndpoint := by
  unfold circleEndpoint
  fun_prop

lemma realEndpoint_measurable : Measurable realEndpoint := by
  apply Measurable.of_eval
  intro i
  exact (CocycleSupport.measurePreserving_circleRepresentative.measurable).comp
    (measurable_pi_apply i)

lemma measurePreserving_circleQuotient :
    MeasurePreserving (fun x : ℝ => (x : Circle)) baseLaw circleMeasure := by
  rw [baseLaw_eq_restrict]
  change MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
    (volume.restrict (Ico 0 1)) volume
  rw [restrict_Ico_eq_restrict_Ioc]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

lemma measurePreserving_circleEndpoint :
    MeasurePreserving circleEndpoint baseMeasure ProductModel.baseMeasure := by
  refine ⟨circleEndpoint_measurable, ?_⟩
  change (Measure.infinitePi (fun _ : ℕ => baseLaw)).map
    (fun x i => (x i : Circle)) = Measure.infinitePi (fun _ : ℕ => circleMeasure)
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => baseLaw)
    (fun _ => measurePreserving_circleQuotient.measurable)]
  simp_rw [measurePreserving_circleQuotient.map_eq]

lemma measurePreserving_realEndpoint :
    MeasurePreserving realEndpoint ProductModel.baseMeasure baseMeasure := by
  refine ⟨realEndpoint_measurable, ?_⟩
  change (Measure.infinitePi (fun _ : ℕ => circleMeasure)).map
    (fun x i => circleRepresentative (x i)) = Measure.infinitePi (fun _ : ℕ => baseLaw)
  unfold circleRepresentative
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => circleMeasure)
    (fun _ => CocycleSupport.measurePreserving_circleRepresentative.measurable)]
  congr 1
  funext i
  exact CocycleSupport.measurePreserving_circleRepresentative.map_eq.trans
    baseLaw_eq_restrict.symm

lemma circleEndpoint_realEndpoint (x : ProductModel.Base) :
    circleEndpoint (realEndpoint x) = x := by
  funext i
  exact AddCircle.coe_equivIco

lemma realEndpoint_circleEndpoint_of_mem {x : Endpoint}
    (hx : ∀ i, x i ∈ Ico (0 : ℝ) 1) : realEndpoint (circleEndpoint x) = x := by
  funext i
  exact AddCircle.equivIco_coe_of_mem (by simpa using hx i)

lemma ae_realEndpoint_circleEndpoint :
    ∀ᵐ x ∂baseMeasure, realEndpoint (circleEndpoint x) = x := by
  have h : ∀ᵐ x ∂baseMeasure, ∀ i, x i ∈ Ico (0 : ℝ) 1 := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => baseLaw) i).quasiMeasurePreserving.ae
      (CouplingMixture.intervalLaw_ae_mem 0 1)
  exact h.mono (fun _ hx => realEndpoint_circleEndpoint_of_mem hx)

theorem circle_density_transport {g : Endpoint → ℝ} (hg : MemLp g 2 baseMeasure) :
    (baseMeasure.withDensity (fun x => ENNReal.ofReal (g x))).map circleEndpoint =
      ProductModel.baseMeasure.withDensity
        (fun x => ENNReal.ofReal (g (realEndpoint x))) ∧
      eLpNorm (g ∘ realEndpoint) 2 ProductModel.baseMeasure = eLpNorm g 2 baseMeasure :=
  DensityTransport.real_density_transport_ae circleEndpoint_measurable realEndpoint_measurable
    measurePreserving_circleEndpoint.map_eq ae_realEndpoint_circleEndpoint hg.aemeasurable

lemma circleHybridEndpoint_measurable (ε : ℕ → Bool) :
    Measurable (circleHybridEndpoint ε) :=
  circleEndpoint_measurable.comp (hybridEndpoint_measurable ε)

lemma circleLeftEndpoint_measurable : Measurable circleLeftEndpoint :=
  circleEndpoint_measurable.comp leftEndpoint_measurable

lemma circleRightEndpoint_measurable : Measurable circleRightEndpoint :=
  circleEndpoint_measurable.comp rightEndpoint_measurable

instance circlePairLaw_probability (P : Parameters) : IsProbabilityMeasure (circlePairLaw P) := by
  unfold circlePairLaw
  infer_instance

theorem exists_circle_hybrid_density (P : Parameters) (ε : ℕ → Bool) {C : ℝ}
    (hsum : Summable (energyBound P)) (hC : (∑' i, energyBound P i) ≤ C) :
    ∃ G : ProductModel.Base → ℝ,
      MemLp G 2 ProductModel.baseMeasure ∧ (0 ≤ᵐ[ProductModel.baseMeasure] G) ∧
      (∫ x, G x ∂ProductModel.baseMeasure) = 1 ∧
      eLpNorm G 2 ProductModel.baseMeasure ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (law P).map (circleHybridEndpoint ε) =
        ProductModel.baseMeasure.withDensity (fun x => ENNReal.ofReal (G x)) := by
  obtain ⟨g, hg, hn, hm, hnorm, hlaw⟩ := exists_hybrid_density P ε hsum hC
  have ht := circle_density_transport hg
  refine ⟨g ∘ realEndpoint, hg.comp_measurePreserving measurePreserving_realEndpoint,
    measurePreserving_realEndpoint.quasiMeasurePreserving.ae hn, ?_, ht.2.trans_le hnorm, ?_⟩
  · have hi := integral_map realEndpoint_measurable.aemeasurable
      (show AEStronglyMeasurable g (ProductModel.baseMeasure.map realEndpoint) by
        rw [measurePreserving_realEndpoint.map_eq]
        exact hg.aestronglyMeasurable)
    rw [measurePreserving_realEndpoint.map_eq] at hi
    exact hi.symm.trans hm
  · change (law P).map (circleEndpoint ∘ hybridEndpoint ε) = _
    rw [← Measure.map_map circleEndpoint_measurable (hybridEndpoint_measurable ε), hlaw]
    exact ht.1

theorem leftEndpoint_ae_mem_unit (P : Parameters) :
    ∀ᵐ ω ∂law P, ∀ i, leftEndpoint ω i ∈ Ico (0 : ℝ) 1 := by
  apply ae_all_iff.2
  intro i
  have hc : ∀ᵐ z ∂coordinateLaw P i, z.2.1 ∈ Ico (0 : ℝ) 1 := by
    apply (ae_map_iff (measurable_fst.comp measurable_snd).aemeasurable measurableSet_Ico).1
    change ∀ᵐ x ∂(coordinateLaw P i).map (fun z => z.2.1), x ∈ Ico (0 : ℝ) 1
    rw [coordinateLaw_map_left]
    exact (withDensity_absolutelyContinuous _ _).ae_le (CouplingMixture.intervalLaw_ae_mem 0 1)
  exact (measurePreserving_eval_infinitePi (coordinateLaw P) i).quasiMeasurePreserving.ae hc

theorem rightEndpoint_ae_mem_unit (P : Parameters) :
    ∀ᵐ ω ∂law P, ∀ i, rightEndpoint ω i ∈ Ico (0 : ℝ) 1 := by
  apply ae_all_iff.2
  intro i
  have hc : ∀ᵐ z ∂coordinateLaw P i, z.2.2 ∈ Ico (0 : ℝ) 1 := by
    apply (ae_map_iff (measurable_snd.comp measurable_snd).aemeasurable measurableSet_Ico).1
    change ∀ᵐ x ∂(coordinateLaw P i).map (fun z => z.2.2), x ∈ Ico (0 : ℝ) 1
    rw [coordinateLaw_map_right]
    exact (withDensity_absolutelyContinuous _ _).ae_le (CouplingMixture.intervalLaw_ae_mem 0 1)
  exact (measurePreserving_eval_infinitePi (coordinateLaw P) i).quasiMeasurePreserving.ae hc

theorem ae_real_circle_endpoints (P : Parameters) :
    ∀ᵐ ω ∂law P, realEndpoint (circleLeftEndpoint ω) = leftEndpoint ω ∧
      realEndpoint (circleRightEndpoint ω) = rightEndpoint ω := by
  filter_upwards [leftEndpoint_ae_mem_unit P, rightEndpoint_ae_mem_unit P] with ω hx hy
  exact ⟨realEndpoint_circleEndpoint_of_mem hx, realEndpoint_circleEndpoint_of_mem hy⟩

theorem ae_circle_endpoints_ordered (P : Parameters) :
    ∀ᵐ ω ∂law P, ProductModel.Ordered (circleLeftEndpoint ω) (circleRightEndpoint ω) := by
  filter_upwards [ae_real_circle_endpoints P, ae_ordered P] with ω hrep hord
  change realEndpoint (circleLeftEndpoint ω) ≤ realEndpoint (circleRightEndpoint ω)
  rw [hrep.1, hrep.2]
  exact hord

theorem circlePairLaw_fst (P : Parameters) :
    (circlePairLaw P).map Prod.fst = (law P).map circleLeftEndpoint := by
  rw [circlePairLaw, Measure.map_map measurable_fst
    (circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable)]
  rfl

theorem circlePairLaw_snd (P : Parameters) :
    (circlePairLaw P).map Prod.snd = (law P).map circleRightEndpoint := by
  rw [circlePairLaw, Measure.map_map measurable_snd
    (circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable)]
  rfl

theorem circlePairLaw_ordered (P : Parameters) :
    ∀ᵐ xy ∂circlePairLaw P, ProductModel.Ordered xy.1 xy.2 := by
  have hm : MeasurableSet {xy : ProductModel.Base × ProductModel.Base |
      ProductModel.Ordered xy.1 xy.2} := by
    change MeasurableSet {xy : ProductModel.Base × ProductModel.Base |
      ∀ i, realEndpoint xy.1 i ≤ realEndpoint xy.2 i}
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le
      ((measurable_pi_apply i).comp (realEndpoint_measurable.comp measurable_fst))
      ((measurable_pi_apply i).comp (realEndpoint_measurable.comp measurable_snd))
  exact (ae_map_iff
    (circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable).aemeasurable hm).2
    (ae_circle_endpoints_ordered P)

end Invariant233.OrderedProductCoupling

end

end OAI
