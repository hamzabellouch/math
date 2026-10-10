import OAI.Probability.FreeIsing.Estimates.FairSpin
import OAI.Probability.FreeIsing.Trees.ConnectedHull

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.LabelDecomposition

theorem indepFun_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    IndepFun (fun U : ι → A => U r)
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i)
      (Measure.infinitePi μ) := by
  have hi : iIndepFun (fun i (U : ι → A) => U i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (X := fun _ a => a) (fun _ => measurable_id)
  have hle : ∀ i : ι,
      MeasurableSpace.comap (fun U : ι → A => U i) inferInstance ≤
        (inferInstance : MeasurableSpace (ι → A)) :=
    fun i => measurable_iff_comap_le.mp (measurable_pi_apply i)
  have hd : Disjoint ({r} : Set ι) {i | i ≠ r} := by simp
  have h := indep_iSup_of_disjoint hle hi hd
  change Indep (MeasurableSpace.comap (fun U : ι → A => U r) inferInstance)
    (MeasurableSpace.comap
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i) inferInstance)
    (Measure.infinitePi μ)
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, Set.mem_ofPred_eq, iSup_iSup_eq_left] using h

theorem map_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    (Measure.infinitePi μ).map
      (fun U : ι → A => (U r, fun i : {i : ι // i ≠ r} => U i)) =
      (μ r).prod (Measure.infinitePi (fun i : {i : ι // i ≠ r} => μ i)) := by
  rw [(indepFun_coordinate_rest μ r).map_prod_eq_prod_map_map
    (measurable_pi_apply r).aemeasurable
      ((measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1)).aemeasurable)]
  rw [Measure.infinitePi_map_eval,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective]

theorem indepFun_fairSpin_rest (d : ℕ) (r : TreeVertex d) :
    IndepFun (fun U : TreeVertex d → ℝ => fairSpin (U r))
      (fun U : TreeVertex d → ℝ => fun v : {v : TreeVertex d // v ≠ r} => U v)
      (labelMeasure d) := by
  exact (indepFun_coordinate_rest (fun _ : TreeVertex d => uniform01) r).comp
    measurable_fairSpin measurable_id

theorem map_fairSpin_rest (d : ℕ) (r : TreeVertex d) :
    (labelMeasure d).map
      (fun U => (fairSpin (U r), fun v : {v : TreeVertex d // v ≠ r} => U v)) =
      (uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : {v : TreeVertex d // v ≠ r} => uniform01)) := by
  change (Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map _ = _
  have hrest : Measurable
      (fun U : TreeVertex d → ℝ => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v)) :=
    (measurable_pi_apply r).prodMk
      (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1))
  calc
    _ = ((Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map
        (fun U => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v))).map
          (Prod.map fairSpin id) := by
      rw [Measure.map_map (measurable_fairSpin.prodMap measurable_id) hrest]
      rfl
    _ = _ := by
      rw [map_coordinate_rest,
        ← Measure.map_prod_map _ _ measurable_fairSpin measurable_id, Measure.map_id]

theorem fairSpin_map_singleton (a : IsingSpin) :
    (uniform01.map fairSpin) {a} = 1 / 2 := by
  rw [Measure.map_apply measurable_fairSpin (show MeasurableSet {a} from trivial)]
  exact fairSpin_mass a

theorem fairSpin_rest_event (d : ℕ) (r : TreeVertex d) (a : IsingSpin)
    (E : Set ({v : TreeVertex d // v ≠ r} → ℝ)) (hE : MeasurableSet E) :
    labelMeasure d {U | fairSpin (U r) = a ∧ (fun v : {v : TreeVertex d // v ≠ r} => U v) ∈ E} =
      (1 / 2 : ENNReal) *
        Measure.infinitePi (fun _ : {v : TreeVertex d // v ≠ r} => uniform01) E := by
  have hm : Measurable (fun U : TreeVertex d → ℝ =>
      (fairSpin (U r), fun v : {v : TreeVertex d // v ≠ r} => U v)) :=
    (measurable_fairSpin.comp (measurable_pi_apply r)).prodMk
      (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1))
  change labelMeasure d ((fun U : TreeVertex d → ℝ =>
    (fairSpin (U r), fun v : {v : TreeVertex d // v ≠ r} => U v)) ⁻¹'
      ({a} ×ˢ E)) = _
  rw [← Measure.map_apply hm ((show MeasurableSet {a} from trivial).prod hE),
    map_fairSpin_rest, Measure.prod_prod, fairSpin_map_singleton]

end Problem367.LabelDecomposition

end

end OAI
