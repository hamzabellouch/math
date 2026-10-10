import OAI.MeasureTheory.Falconer.Estimates.FourPointPartition
import OAI.MeasureTheory.Falconer.Estimates.FarCellCount

namespace OAI

/-! # Rebinning the original four-point law at the comparable depth

The earlier labels do not occur in this identity. Only the common-depth
partners forced by the two actual point displacements survive.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem fourPointChildMeasure_restrict_eq_zero {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : 0 < Q.side) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ)
    (u v : List (Fin d → Bool) × List (Fin d → Bool))
    (hu : u ∈ P.occupiedPaths μ n ×ˢ P.occupiedPaths μ n)
    (hv : v ∈ Q.occupiedPaths ν n ×ˢ Q.occupiedPaths ν n)
    (U : Set ((Space d × Space d) × (Space d × Space d))) (hU : MeasurableSet U)
    (hgeo : ∀ z ∈ U,
      (256*((d:ℝ)+1)*(P.side/(2:ℝ)^n) < dist z.1.1 z.1.2 ∧
        dist z.1.1 z.1.2 ≤ 1024*((d:ℝ)+1)*(P.side/(2:ℝ)^n)) ∧
      (256*((d:ℝ)+1)*(Q.side/(2:ℝ)^n) < dist z.2.1 z.2.2 ∧
        dist z.2.1 z.2.2 ≤ 1024*((d:ℝ)+1)*(Q.side/(2:ℝ)^n)))
    (hbad : (u,v) ∉ farCellPartners P μ n ×ˢ farCellPartners Q ν n) :
    (fourPointChildMeasure P Q μ ν u v).restrict U = 0 := by
  simp only [fourPointChildMeasure, Measure.prod_restrict, Measure.restrict_restrict hU]
  have he : U ∩ (((P.descendant u.1).carrier ×ˢ (P.descendant u.2).carrier) ×ˢ
      ((Q.descendant v.1).carrier ×ˢ (Q.descendant v.2).carrier)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hp,hq⟩ := hgeo z hz.1
    exact hbad (Finset.mem_product.mpr
      ⟨farCellPartners_of_comparable_points P hP μ n u hu hz.2.1.1 hz.2.1.2 hp.1 hp.2,
        farCellPartners_of_comparable_points Q hQ ν n v hv hz.2.2.1 hz.2.2.2 hq.1 hq.2⟩)
  rw [he, Measure.restrict_empty]

theorem originalFourPointMeasure_far_partition {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : 0 < Q.side) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ)
    (U : Set ((Space d × Space d) × (Space d × Space d))) (hU : MeasurableSet U)
    (hgeo : ∀ z ∈ U,
      (256*((d:ℝ)+1)*(P.side/(2:ℝ)^n) < dist z.1.1 z.1.2 ∧
        dist z.1.1 z.1.2 ≤ 1024*((d:ℝ)+1)*(P.side/(2:ℝ)^n)) ∧
      (256*((d:ℝ)+1)*(Q.side/(2:ℝ)^n) < dist z.2.1 z.2.2 ∧
        dist z.2.1 z.2.2 ≤ 1024*((d:ℝ)+1)*(Q.side/(2:ℝ)^n))) :
    (originalFourPointMeasure P Q μ ν).restrict U =
      ∑ z ∈ farCellPartners P μ n ×ˢ farCellPartners Q ν n,
        (fourPointChildMeasure P Q μ ν z.1 z.2).restrict U := by
  rw [originalFourPointMeasure_partition P Q μ ν n,
    PlanarFalconer.finite_measure_restrict_sum]
  simp only [PlanarFalconer.finite_measure_restrict_sum]
  rw [← Finset.sum_product (P.occupiedPaths μ n ×ˢ P.occupiedPaths μ n)
    (Q.occupiedPaths ν n ×ˢ Q.occupiedPaths ν n)
    (fun z => (fourPointChildMeasure P Q μ ν z.1 z.2).restrict U)]
  symm
  apply Finset.sum_subset
  · intro z hz
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hz
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hu).1,(Finset.mem_filter.mp hv).1⟩
  · intro z hz hbad
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hz
    exact fourPointChildMeasure_restrict_eq_zero P Q hP hQ μ ν n z.1 z.2 hu hv U hU hgeo hbad

end Falconer

end OAI
