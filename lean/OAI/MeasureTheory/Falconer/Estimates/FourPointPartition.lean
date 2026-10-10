import OAI.MeasureTheory.Falconer.Estimates.RetainedPairs
import OAI.MeasureTheory.Falconer.Graphs.NearGraph

namespace OAI

/-! # Exact original four-point partitions before far rebinning

Each internal pair keeps its original two endpoint restrictions. These
identities allow a nonnegative kernel bound to discard a far-label
selection and then repartition at the common comparable-displacement depth.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def originalFourPointMeasure {d : ℕ} (P Q : DyadicCube d)
    (μ ν : Measure (Space d)) : Measure ((Space d × Space d) × (Space d × Space d)) :=
  ((μ.restrict P.carrier).prod (μ.restrict P.carrier)).prod
    ((ν.restrict Q.carrier).prod (ν.restrict Q.carrier))

noncomputable def fourPointChildMeasure {d : ℕ} (P Q : DyadicCube d)
    (μ ν : Measure (Space d))
    (u v : List (Fin d → Bool) × List (Fin d → Bool)) :
    Measure ((Space d × Space d) × (Space d × Space d)) :=
  ((μ.restrict (P.descendant u.1).carrier).prod (μ.restrict (P.descendant u.2).carrier)).prod
    ((ν.restrict (Q.descendant v.1).carrier).prod (ν.restrict (Q.descendant v.2).carrier))

theorem DyadicCube.pair_restrict_occupiedPaths {d : ℕ} (P : DyadicCube d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (n : ℕ) :
    (μ.restrict P.carrier).prod (μ.restrict P.carrier) =
      ∑ u ∈ P.occupiedPaths μ n ×ˢ P.occupiedPaths μ n,
        (μ.restrict (P.descendant u.1).carrier).prod (μ.restrict (P.descendant u.2).carrier) := by
  rw [P.restrict_occupiedPaths μ n,PlanarFalconer.finite_measure_prod_sum,Finset.sum_product]

theorem originalFourPointMeasure_partition {d : ℕ} (P Q : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ) :
    originalFourPointMeasure P Q μ ν =
      ∑ u ∈ P.occupiedPaths μ n ×ˢ P.occupiedPaths μ n,
        ∑ v ∈ Q.occupiedPaths ν n ×ˢ Q.occupiedPaths ν n,
          fourPointChildMeasure P Q μ ν u v := by
  rw [originalFourPointMeasure,P.pair_restrict_occupiedPaths μ n,
    Q.pair_restrict_occupiedPaths ν n,PlanarFalconer.finite_measure_prod_sum]
  rfl

theorem originalFourPoint_lintegral_drop_selection {d : ℕ} (P Q : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ)
    (F : ((Space d × Space d) × (Space d × Space d)) → ℝ≥0∞)
    (U : (List (Fin d → Bool) × List (Fin d → Bool)) →
      (List (Fin d → Bool) × List (Fin d → Bool)) →
        Set ((Space d × Space d) × (Space d × Space d))) :
    (∑ u ∈ P.occupiedPaths μ n ×ˢ P.occupiedPaths μ n,
      ∑ v ∈ Q.occupiedPaths ν n ×ˢ Q.occupiedPaths ν n,
        ∫⁻ z in U u v, F z ∂fourPointChildMeasure P Q μ ν u v) ≤
      ∫⁻ z, F z ∂originalFourPointMeasure P Q μ ν := by
  rw [originalFourPointMeasure_partition P Q μ ν n]
  simp only [lintegral_finsetSum_measure]
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)

end Falconer

end OAI
