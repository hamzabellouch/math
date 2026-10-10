import OAI.MeasureTheory.Falconer.Estimates.FinitePartitionMask

namespace OAI

/-! # Exact weighted law of a mask assembled on finitely many regions -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X ι : Type*} [MeasurableSpace X]

theorem withDensity_finset_sum (π : Measure X) (F : Finset ι) (f : ι → X → ℝ≥0∞)
    (hf : ∀ i ∈ F, Measurable (f i)) :
    π.withDensity (fun x => ∑ i ∈ F, f i x) = ∑ i ∈ F, π.withDensity (f i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    have he : (fun x => ∑ i ∈ insert a F, f i x) =
        f a + (fun x => ∑ i ∈ F, f i x) := by ext x; simp [ha]
    rw [he,withDensity_add_left (hf a (Finset.mem_insert_self a F)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)),Finset.sum_insert ha]

theorem finitePartitionMask_weighted_measure (π : Measure X) (F : Finset ι)
    (C : ι → Set X) (w : X → ℝ) (v : ι → X → ℝ)
    (hC : ∀ i ∈ F, MeasurableSet (C i)) (hw : Measurable w)
    (hv : ∀ i ∈ F, Measurable (v i))
    (hw0 : ∀ x, 0 ≤ w x) (hv0 : ∀ i ∈ F, ∀ x, 0 ≤ v i x) :
    π.withDensity (fun x => ENNReal.ofReal (w x * finitePartitionMask F C v x)) =
      ∑ i ∈ F, (π.restrict (C i)).withDensity (fun x => ENNReal.ofReal (w x*v i x)) := by
  classical
  have he : (fun x => ENNReal.ofReal (w x * finitePartitionMask F C v x)) =
      (fun x => ∑ i ∈ F, (C i).indicator (fun y => ENNReal.ofReal (w y*v i y)) x) := by
    funext x
    rw [finitePartitionMask,Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hx : x ∈ C i <;> simp [hx]
    · intro i hi
      exact mul_nonneg (hw0 x) (indicator_nonneg (fun y _ => hv0 i hi y) x)
  rw [he,withDensity_finset_sum π F
    (fun i x => (C i).indicator (fun y => ENNReal.ofReal (w y*v i y)) x)
    (fun i hi => ((hw.mul (hv i hi)).ennreal_ofReal.indicator (hC i hi)))]
  apply Finset.sum_congr rfl
  intro i hi
  exact withDensity_indicator (hC i hi) _

theorem finitePartitionMask_weighted_map (π : Measure X) (F : Finset ι)
    (C : ι → Set X) (w : X → ℝ) (v : ι → X → ℝ) (f : X → ℝ)
    (hC : ∀ i ∈ F, MeasurableSet (C i)) (hw : Measurable w)
    (hv : ∀ i ∈ F, Measurable (v i)) (hf : Measurable f)
    (hw0 : ∀ x, 0 ≤ w x) (hv0 : ∀ i ∈ F, ∀ x, 0 ≤ v i x) :
    (π.withDensity (fun x => ENNReal.ofReal (w x * finitePartitionMask F C v x))).map f =
      ∑ i ∈ F, ((π.restrict (C i)).withDensity (fun x => ENNReal.ofReal (w x*v i x))).map f := by
  rw [finitePartitionMask_weighted_measure π F C w v hC hw hv hw0 hv0,
    ← Measure.sum_coe_finset,Measure.map_sum hf.aemeasurable]
  exact Measure.sum_coe_finset F
    (fun i => ((π.restrict (C i)).withDensity (fun x => ENNReal.ofReal (w x*v i x))).map f)

end Falconer

end OAI
