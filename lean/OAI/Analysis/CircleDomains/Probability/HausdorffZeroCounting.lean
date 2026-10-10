import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Count

namespace OAI

/-! Zero-dimensional Hausdorff measure counts the points of an arbitrary
set. Finite subsets suffice for the lower bound on infinite sets. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma hausdorff_zero_finset {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (F : Finset X) :
    (μH[0] : Measure X) (F : Set X) = F.card := by
  rw [← sum_measure_singleton]
  simp only [Measure.hausdorffMeasure_zero_singleton, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma hausdorff_zero_eq_count {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (A : Set X) :
    (μH[0] : Measure X) A = Measure.count A := by
  classical
  by_cases hA : A.Finite
  · rw [← hA.coe_toFinset, hausdorff_zero_finset, Measure.count_apply_finset]
  · have hA : A.Infinite := hA
    rw [Measure.count_apply_infinite hA]
    apply top_unique
    apply le_of_tendsto' ENNReal.tendsto_nat_nhds_top
    intro n
    obtain ⟨F, hFA, hF⟩ := hA.exists_subset_card_eq n
    rw [← hF, ← hausdorff_zero_finset F]
    exact measure_mono hFA

end CircleDomainRigidity

end

end OAI
