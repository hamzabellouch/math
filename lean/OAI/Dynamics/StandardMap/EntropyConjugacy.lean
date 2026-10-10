import OAI.Dynamics.StandardMap.NoCriticalSequence

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
noncomputable def coordinatePartition {r:ℕ} (p:FinitePartition r) : FinitePartition r :=
  ⟨p.val ∘ recurrenceCoordinates,p.property.comp measurePreserving_recurrenceCoordinates.measurable⟩
lemma coordinate_blockAtom {r:ℕ} (k:ℝ) (p:FinitePartition r) (n:ℕ) (w:Fin n → Fin (r+1)) :
    blockAtom (standardMap k) (coordinatePartition p) n w=
      recurrenceCoordinates ⁻¹' blockAtom (torusStep k) p n w := by
  have hc:Function.Semiconj recurrenceCoordinates (standardMap k) (torusStep k) := standardMap_conjugacy k
  ext z
  simp only [blockAtom,mem_ofPred_eq,mem_preimage,coordinatePartition,Function.comp_apply]
  simp only [hc.iterate_right _ _]
lemma coordinate_blockEntropy {r:ℕ} (k:ℝ) (p:FinitePartition r) (n:ℕ) :
    blockEntropy area (standardMap k) (coordinatePartition p) n=blockEntropy area (torusStep k) p n := by
  unfold blockEntropy
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  rw [coordinate_blockAtom,measurePreserving_recurrenceCoordinates.measure_preimage
    (blockAtom_measurable _ (continuous_torusStep k).measurable p n w).nullMeasurableSet]
lemma coordinate_partitionEntropy {r:ℕ} (k:ℝ) (p:FinitePartition r) :
    partitionEntropy area (standardMap k) (coordinatePartition p)=partitionEntropy area (torusStep k) p := by
  unfold partitionEntropy
  simp only [coordinate_blockEntropy]
lemma metricEntropy_standardMap_ge_partition {r:ℕ} (k:ℝ) (p:FinitePartition r) :
    partitionEntropy area (torusStep k) p≤ metricEntropy area (standardMap k) := by
  rw [← coordinate_partitionEntropy]
  exact le_iSup_of_le r (le_iSup_of_le (coordinatePartition p) le_rfl)
end StandardMapEntropy

end OAI
