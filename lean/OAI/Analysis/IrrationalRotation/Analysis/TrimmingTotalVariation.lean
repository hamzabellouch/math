import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Invariant233.TailTrimming

theorem totalVariation_sub_restrict {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (A : Set X) (hA : MeasurableSet A) :
    (μ.toSignedMeasure - (μ.restrict A).toSignedMeasure).totalVariation =
      μ.restrict Aᶜ := by
  rw [SignedMeasure.totalVariation, Measure.toJordanDecomposition_toSignedMeasure_sub]
  change (μ - μ.restrict A) + (μ.restrict A - μ) = μ.restrict Aᶜ
  rw [Measure.sub_eq_zero_of_le Measure.restrict_le_self, add_zero]
  calc
    μ - μ.restrict A = (μ.restrict Aᶜ + μ.restrict A) - μ.restrict A := by
      rw [Measure.restrict_compl_add_restrict hA]
    _ = μ.restrict Aᶜ := Measure.add_sub_cancel

theorem totalVariation_sub_restrict_univ {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (A : Set X) (hA : MeasurableSet A) :
    (μ.toSignedMeasure - (μ.restrict A).toSignedMeasure).totalVariation univ = μ Aᶜ := by
  rw [totalVariation_sub_restrict μ A hA, Measure.restrict_apply MeasurableSet.univ,
    univ_inter]

theorem tendsto_totalVariation_sub_restrict {X J : Type*} [MeasurableSpace X]
    {l : Filter J} (μ : J → Measure X) (hμ : ∀ j, IsFiniteMeasure (μ j))
    (A : J → Set X) (hA : ∀ j, MeasurableSet (A j))
    (hlost : Tendsto (fun j => μ j (A j)ᶜ) l (𝓝 0)) :
    Tendsto (fun j => ((μ j).toSignedMeasure - ((μ j).restrict (A j)).toSignedMeasure).totalVariation univ) l (𝓝 0) := by
  have heq (j : J) := by
    letI := hμ j
    exact totalVariation_sub_restrict_univ (μ j) (A j) (hA j)
  simpa only [heq] using hlost

end Invariant233.TailTrimming

end

end OAI
