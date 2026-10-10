import OAI.Analysis.IrrationalRotation.Sampling.ProductIdealSamplingScales
import OAI.Analysis.IrrationalRotation.Sampling.SamplingCylinderWeak

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators

namespace Invariant233.ProductModel.IdealSampling
open SamplingCylinderWeak

private theorem mem_frontier_preimage_of_continuousAt
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} {s : Set Y} (hf : ContinuousAt f x)
    (hx : x ∈ frontier (f ⁻¹' s)) : f x ∈ frontier s := by
  rw [frontier_eq_closure_inter_closure] at hx ⊢
  constructor
  · exact closure_mono (image_preimage_subset f s) (mem_closure_image hf hx.1)
  · exact closure_mono (image_preimage_subset f sᶜ) (mem_closure_image hf hx.2)

private theorem null_frontier_preimage_of_ae_continuousAt
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] {μ : Measure X} {f : X → Y} {s : Set Y}
    (hf : ∀ᵐ x ∂μ, ContinuousAt f x) (hs : μ (f ⁻¹' frontier s) = 0) :
    μ (frontier (f ⁻¹' s)) = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hf, measure_eq_zero_iff_ae_notMem.mp hs] with x hfx hsx
  exact fun hx => hsx (mem_frontier_preimage_of_continuousAt hfx hx)

theorem triangularLaw_coordinate_singleton (I : Finset ℕ) (b : Bool) (i : ℕ)
    (a : Circle) :
    triangularLaw I {xy | (if b then xy.2 i else xy.1 i) = a} = 0 := by
  have hfst : (baseMeasure.prod baseMeasure) {xz : EndpointPair | xz.1 i = a} = 0 := by
    have hp := (measurePreserving_eval_infinitePi (fun _ : ℕ => circleMeasure) i).comp
      (measurePreserving_fst (μ := baseMeasure) (ν := baseMeasure))
    have he := hp.measure_preimage (measurableSet_singleton a).nullMeasurableSet
    simpa [Sampling.circleMeasure_singleton, Function.comp_def, Set.preimage, Set.mem_singleton_iff] using he
  have hsnd : (baseMeasure.prod baseMeasure) {xz : EndpointPair | xz.2 i = a} = 0 := by
    have hp := (measurePreserving_eval_infinitePi (fun _ : ℕ => circleMeasure) i).comp
      (measurePreserving_snd (μ := baseMeasure) (ν := baseMeasure))
    have he := hp.measure_preimage (measurableSet_singleton a).nullMeasurableSet
    simpa [Sampling.circleMeasure_singleton, Function.comp_def, Set.preimage, Set.mem_singleton_iff] using he
  rw [triangularLaw, Measure.map_apply (Sampling.endpointMap_measurable I)]
  · apply le_antisymm ((Measure.restrict_le_self _).trans_eq ?_) (bot_le)
    cases b
    · simpa using hfst
    · by_cases hi : i ∈ I
      · simpa [selectedEndpoint, hi] using hsnd
      · simpa [selectedEndpoint, hi] using hfst
  · cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_fst) measurable_const
    · exact measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_snd) measurable_const

theorem triangularLaw_cutCoordinate_singleton (I : Finset ℕ) (k : Bool × ℕ)
    (a : ℝ) : triangularLaw I {xy | cutCoordinates xy k = a} = 0 := by
  apply measure_mono_null _ (triangularLaw_coordinate_singleton I k.1 k.2 (a : Circle))
  intro xy hxy
  change circleRepresentative (if k.1 then xy.2 k.2 else xy.1 k.2) = a at hxy
  change (if k.1 then xy.2 k.2 else xy.1 k.2) = (a : Circle)
  rw [← hxy]
  exact AddCircle.coe_equivIco.symm

theorem triangularLaw_ae_continuousAt_cutCoordinate (I : Finset ℕ) (k : Bool × ℕ) :
    ∀ᵐ xy ∂triangularLaw I, ContinuousAt (fun z => cutCoordinates z k) xy := by
  have hn : ∀ᵐ xy ∂triangularLaw I,
      (if k.1 then xy.2 k.2 else xy.1 k.2) ≠ (0 : Circle) :=
    by simpa only [not_not] using (ae_iff.mpr (by
      simpa only [not_not] using triangularLaw_coordinate_singleton I k.1 k.2 0))
  filter_upwards [hn] with xy hxy
  have hc : Continuous (fun z : EndpointPair => if k.1 then z.2 k.2 else z.1 k.2) := by
    cases k.1 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  have hr : ContinuousAt circleRepresentative (if k.1 then xy.2 k.2 else xy.1 k.2) :=
    continuousAt_subtype_val.comp (AddCircle.continuousAt_equivIco (1 : ℝ) 0 hxy)
  exact hr.comp (f := fun z : EndpointPair => if k.1 then z.2 k.2 else z.1 k.2) hc.continuousAt

theorem triangularLaw_null_frontier_interval (I : Finset ℕ) (k : Bool × ℕ)
    (a b : ℝ) :
    triangularLaw I (frontier {xy | a < cutCoordinates xy k ∧ cutCoordinates xy k < b}) = 0 := by
  change triangularLaw I (frontier ((fun xy => cutCoordinates xy k) ⁻¹' Ioo a b)) = 0
  apply null_frontier_preimage_of_ae_continuousAt
    (triangularLaw_ae_continuousAt_cutCoordinate I k)
  by_cases hab : a < b
  · rw [frontier_Ioo hab]
    have he : (fun xy => cutCoordinates xy k) ⁻¹' ({a, b} : Set ℝ) =
        {xy | cutCoordinates xy k = a} ∪ {xy | cutCoordinates xy k = b} := by
      ext xy
      simp
    rw [he]
    exact measure_union_null (triangularLaw_cutCoordinate_singleton I k a)
      (triangularLaw_cutCoordinate_singleton I k b)
  · simp [Set.Ioo_eq_empty hab]

theorem triangularLaw_null_frontier_endpointCylinder (I : Finset ℕ)
    (t : CylinderTest (Bool × ℕ)) :
    triangularLaw I (frontier (endpointCylinder t)) = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [endpointCylinder]
  | @insert v t hv ih =>
    have he : endpointCylinder (insert v t) =
        {xy | (v.2.1 : ℝ) < cutCoordinates xy v.1 ∧
          cutCoordinates xy v.1 < (v.2.2 : ℝ)} ∩ endpointCylinder t := by
      ext xy
      simp [endpointCylinder, SamplingCylinderWeak.cylinder]
    rw [he]
    apply measure_mono_null (frontier_inter_subset _ _)
    exact measure_union_null
      (measure_inter_null_of_null_left _ (triangularLaw_null_frontier_interval I v.1 _ _))
      (measure_inter_null_of_null_right _ ih)

theorem finiteMeasure_tendsto_apply_of_null_frontier
    {X ι : Type*} [Nonempty X] [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {l : Filter ι} {μ : ι → FiniteMeasure X} {ν : FiniteMeasure X}
    (hμ : Tendsto μ l (𝓝 ν)) {E : Set X}
    (hE : (ν : Measure X) (frontier E) = 0) :
    Tendsto (fun i => μ i E) l (𝓝 (ν E)) := by
  by_cases hν : ν = 0
  · subst ν
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ≥0)) l (𝓝 0)))
      (by simpa using hμ.mass)
    · intro i; exact bot_le
    · intro i; exact (μ i).apply_le_mass E
  · have hnorm := FiniteMeasure.tendsto_normalize_of_tendsto hμ hν
    have hEnorm : ν.normalize (frontier E) = 0 := by
      rw [ν.normalize_eq_of_nonzero hν]
      have hzero : ν (frontier E) = 0 := by
        change ((ν : Measure X) (frontier E)).toNNReal = 0
        rw [hE]
        rfl
      rw [hzero, mul_zero]
    have h := hμ.mass.mul
      (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hnorm hEnorm)
    simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using h

theorem cylinder_real_tendsto_of_weaklyConverges
    (I : Finset ℕ) {μ : ℕ → Measure EndpointPair}
    (hfinite : ∀ n, IsFiniteMeasure (μ n))
    (hμ : WeaklyConverges μ (triangularLaw I))
    (t : CylinderTest (Bool × ℕ)) :
    Tendsto (fun n => (μ n).real (endpointCylinder t)) atTop
      (𝓝 ((triangularLaw I).real (endpointCylinder t))) := by
  let μ' : ℕ → FiniteMeasure EndpointPair := fun n => ⟨μ n, hfinite n⟩
  let ν : FiniteMeasure EndpointPair := ⟨triangularLaw I, Sampling.triangularLaw_finite I⟩
  have hw : Tendsto μ' atTop (𝓝 ν) :=
    (weaklyConverges_iff_tendsto μ' ν).mp hμ
  have ht := finiteMeasure_tendsto_apply_of_null_frontier hw
    (triangularLaw_null_frontier_endpointCylinder I t)
  have hr := NNReal.continuous_coe.continuousAt.tendsto.comp ht
  change Tendsto (fun n => (((μ n) (endpointCylinder t)).toNNReal : ℝ)) atTop
    (𝓝 (((triangularLaw I) (endpointCylinder t)).toNNReal : ℝ))
  exact hr

theorem law_cylinder_real_tendsto_of_productScaleLaws (I : Finset ℕ)
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (t : CylinderTest (Bool × ℕ)) :
    Tendsto (fun l => (law I (Finset.range (p.prefixCount (l + 1)))
      ((p.m l : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m l : ℝ) ^ 2)).real
        (endpointCylinder t)) atTop
      (𝓝 ((triangularLaw I).real (endpointCylinder t))) :=
  cylinder_real_tendsto_of_weaklyConverges I (fun _ => inferInstance)
    (law_weaklyConverges_of_productScaleLaws I hp) t

end Invariant233.ProductModel.IdealSampling

end

end OAI
