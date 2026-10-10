import OAI.Analysis.IrrationalRotation.Analysis.TriangularLawMass
import OAI.Analysis.IrrationalRotation.Rotation.CircleRepresentative

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace Invariant233.ProductModel

private theorem rep_measurable : Measurable circleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

private theorem rep_bounds (x : Circle) :
    0 ≤ circleRepresentative x ∧ circleRepresentative x < 1 := by
  simpa [circleRepresentative] using (AddCircle.equivIco (1 : ℝ) 0 x).property

private theorem rep_preserving : MeasurePreserving circleRepresentative circleMeasure
    (volume.restrict (Ico (0 : ℝ) 1)) :=
  CocycleSupport.measurePreserving_circleRepresentative

theorem circleRepresentative_upper_tail (r : ℝ) (hr : 0 ≤ r) :
    circleMeasure {x | r < circleRepresentative x} = ENNReal.ofReal (1 - r) := by
  change circleMeasure (circleRepresentative ⁻¹' Ioi r) = _
  rw [rep_preserving.measure_preimage measurableSet_Ioi.nullMeasurableSet,
    Measure.restrict_apply measurableSet_Ioi]
  have hset : Ioi r ∩ Ico (0 : ℝ) 1 = Ioo r 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ico, mem_Ioo]
    constructor
    · tauto
    · intro hx
      exact ⟨hx.1, le_trans hr hx.1.le, hx.2⟩
  rw [hset, Real.volume_Ioo]

theorem circleRepresentative_lower_tail (r : ℝ) (hr : r ≤ 1) :
    circleMeasure {x | circleRepresentative x < r} = ENNReal.ofReal r := by
  change circleMeasure (circleRepresentative ⁻¹' Iio r) = _
  rw [rep_preserving.measure_preimage measurableSet_Iio.nullMeasurableSet,
    Measure.restrict_apply measurableSet_Iio]
  have hset : Iio r ∩ Ico (0 : ℝ) 1 = Ico 0 r := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ico]
    constructor
    · tauto
    · intro hx
      exact ⟨hx.2, hx.1, lt_of_lt_of_le hx.2 hr⟩
  rw [hset, Real.volume_Ico, sub_zero]

private theorem event_measurable (I : Finset ℕ) : MeasurableSet (triangularEvent I) := by
  simp only [triangularEvent, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt
    (rep_measurable.comp ((measurable_pi_apply i).comp measurable_fst))
    (rep_measurable.comp ((measurable_pi_apply i).comp measurable_snd))

theorem triangularEvent_fiber_mass (I : Finset ℕ) (x : Base) :
    baseMeasure (Prod.mk x ⁻¹' triangularEvent I) =
      ENNReal.ofReal (triangularFirstDensity I x) := by
  change (Measure.infinitePi (fun _ : ℕ => circleMeasure))
    ((I : Set ℕ).pi (fun i => {z | circleRepresentative (x i) < circleRepresentative z})) = _
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_lt measurable_const rep_measurable)]
  simp_rw [circleRepresentative_upper_tail _ (rep_bounds _).1]
  rw [triangularFirstDensity, ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact sub_nonneg.mpr (rep_bounds (x i)).2.le

theorem fst_restrict_prod_eq_withDensity {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite ν] (E : Set (α × β)) (hE : MeasurableSet E) :
    ((μ.prod ν).restrict E).map Prod.fst =
      μ.withDensity (fun x => ν (Prod.mk x ⁻¹' E)) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs,
    Measure.restrict_apply (measurable_fst hs),
    Measure.prod_apply ((measurable_fst hs).inter hE),
    withDensity_apply _ hs, ← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp [hx, Set.preimage, Set.indicator_of_mem]
  · simp [hx, Set.preimage, Set.indicator_of_notMem]

theorem triangularLaw_first_marginal (I : Finset ℕ) :
    (triangularLaw I).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (triangularFirstDensity I x)) := by
  have hm : Measurable (fun xz : EndpointPair => (xz.1, selectedEndpoint I xz.1 xz.2)) := by
    refine measurable_fst.prodMk (Measurable.of_eval fun index => ?_)
    by_cases hi : index ∈ I
    · simpa [selectedEndpoint, hi, Function.comp_def] using
        (measurable_pi_apply index).comp (measurable_snd : Measurable (Prod.snd : EndpointPair → Base))
    · simpa [selectedEndpoint, hi, Function.comp_def] using
        (measurable_pi_apply index).comp (measurable_fst : Measurable (Prod.fst : EndpointPair → Base))
  rw [triangularLaw, Measure.map_map measurable_fst hm]
  change ((baseMeasure.prod baseMeasure).restrict (triangularEvent I)).map Prod.fst = _
  rw [fst_restrict_prod_eq_withDensity _ _ _ (event_measurable I)]
  congr 1
  funext x
  exact triangularEvent_fiber_mass I x

theorem reversedTriangularEvent_fiber_mass (I : Finset ℕ) (x : Base) :
    baseMeasure {z : Base | ∀ i ∈ I,
      circleRepresentative (z i) < circleRepresentative (x i)} =
      ENNReal.ofReal (triangularSecondDensity I x) := by
  change (Measure.infinitePi (fun _ : ℕ => circleMeasure))
    ((I : Set ℕ).pi (fun i => {z | circleRepresentative z < circleRepresentative (x i)})) = _
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_lt rep_measurable measurable_const)]
  simp_rw [circleRepresentative_lower_tail _ (rep_bounds _).2.le]
  rw [triangularSecondDensity, ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact (rep_bounds (x i)).1

theorem reversedTriangularEvent_first_marginal (I : Finset ℕ) :
    ((baseMeasure.prod baseMeasure).restrict
      {xz : EndpointPair | ∀ i ∈ I,
        circleRepresentative (xz.2 i) < circleRepresentative (xz.1 i)}).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (triangularSecondDensity I x)) := by
  rw [fst_restrict_prod_eq_withDensity]
  · congr 1
    funext x
    exact reversedTriangularEvent_fiber_mass I x
  · simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_lt
      (rep_measurable.comp ((measurable_pi_apply i).comp measurable_snd))
      (rep_measurable.comp ((measurable_pi_apply i).comp measurable_fst))

end Invariant233.ProductModel

end

end OAI
