import OAI.MeasureTheory.Falconer.Estimates.SuffixGrouping
import OAI.MeasureTheory.Falconer.Estimates.DyadicTree

namespace OAI

/-! # Exact decomposition into the suffix cells having a witness

Only actual original-law restrictions occur. Empty intersections with the
parent's good-pair set contribute zero, so retaining witnessed cells is an
exact identity, before their full cell measures are used for comparison.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

noncomputable def testedCellPair (μ ν : Measure (Space d))
    (P Q : DyadicCube d) (G : Set (Space d × Space d)) : Measure (Space d × Space d) :=
  ((μ.restrict P.carrier).prod (ν.restrict Q.carrier)).restrict G

noncomputable def testedCellDistance (μ ν : Measure (Space d))
    (P Q : DyadicCube d) (G : Set (Space d × Space d)) : Measure ℝ :=
  (testedCellPair μ ν P Q G).map (fun z => dist z.1 z.2)

instance testedCellPair_finite (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (G : Set (Space d × Space d)) : IsFiniteMeasure (testedCellPair μ ν P Q G) := by
  unfold testedCellPair
  infer_instance

instance testedCellDistance_finite (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (G : Set (Space d × Space d)) : IsFiniteMeasure (testedCellDistance μ ν P Q G) := by
  unfold testedCellDistance
  infer_instance

noncomputable def retainedCellPairs (μ ν : Measure (Space d))
    (P Q : DyadicCube d) (n : ℕ) (G : Set (Space d × Space d)) :
    Finset (List (Fin d → Bool) × List (Fin d → Bool)) :=
  (P.occupiedPaths μ n ×ˢ Q.occupiedPaths ν n).filter fun c =>
    ∃ x ∈ (P.descendant c.1).carrier, ∃ y ∈ (Q.descendant c.2).carrier, (x,y) ∈ G

theorem testedCellPair_eq_zero (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (hw : ¬ ∃ x ∈ P.carrier, ∃ y ∈ Q.carrier, (x,y) ∈ G) :
    testedCellPair μ ν P Q G = 0 := by
  apply Measure.restrict_eq_zero.mpr
  rw [Measure.prod_restrict,Measure.restrict_apply hG]
  have he : G ∩ (P.carrier ×ˢ Q.carrier) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hw ⟨z.1,hz.2.1,z.2,hz.2.2,hz.1⟩
  rw [he,measure_empty]

theorem testedCellPair_split (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (n : ℕ) (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    testedCellPair μ ν P Q G =
      ∑ c ∈ retainedCellPairs μ ν P Q n G,
        testedCellPair μ ν (P.descendant c.1) (Q.descendant c.2) G := by
  rw [testedCellPair,P.restrict_occupiedPaths μ n,Q.restrict_occupiedPaths ν n,
    PlanarFalconer.finite_measure_prod_sum]
  rw [← Finset.sum_product (P.occupiedPaths μ n) (Q.occupiedPaths ν n)
    (fun c : List (Fin d → Bool) × List (Fin d → Bool) =>
      (μ.restrict (P.descendant c.1).carrier).prod (ν.restrict (Q.descendant c.2).carrier)),
    PlanarFalconer.finite_measure_restrict_sum]
  change (∑ c ∈ P.occupiedPaths μ n ×ˢ Q.occupiedPaths ν n,
      testedCellPair μ ν (P.descendant c.1) (Q.descendant c.2) G) = _
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c hc hn
  apply testedCellPair_eq_zero μ ν _ _ G hG
  intro hw
  exact hn (Finset.mem_filter.mpr ⟨hc,hw⟩)

theorem testedCellDistance_split (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (n : ℕ) (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    testedCellDistance μ ν P Q G =
      ∑ c ∈ retainedCellPairs μ ν P Q n G,
        testedCellDistance μ ν (P.descendant c.1) (Q.descendant c.2) G := by
  rw [testedCellDistance,testedCellPair_split μ ν P Q n G hG,
    Measure.map_finset_sum (by fun_prop)]
  rfl

theorem testedCellDistance_le (μ ν : Measure (Space d))
    (P Q : DyadicCube d) (G : Set (Space d × Space d)) :
    testedCellDistance μ ν P Q G ≤ cellDistance μ ν P Q := by
  exact Measure.map_mono Measure.restrict_le_self (by fun_prop)

theorem full_retained_distance_le (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (n : ℕ) (G H : Set (Space d × Space d))
    (hcover : ∀ c ∈ retainedCellPairs μ ν P Q n G,
      (P.descendant c.1).carrier ×ˢ (Q.descendant c.2).carrier ⊆ H) :
    (∑ c ∈ retainedCellPairs μ ν P Q n G,
      cellDistance μ ν (P.descendant c.1) (Q.descendant c.2)) ≤
        testedCellDistance μ ν P Q H := by
  have he (c : List (Fin d → Bool) × List (Fin d → Bool))
      (hc : c ∈ retainedCellPairs μ ν P Q n G) :
      cellDistance μ ν (P.descendant c.1) (Q.descendant c.2) =
        testedCellDistance μ ν (P.descendant c.1) (Q.descendant c.2) H := by
    unfold cellDistance testedCellDistance testedCellPair
    rw [Measure.prod_restrict,Measure.restrict_restrict'
      ((P.descendant c.1).measurable.prod (Q.descendant c.2).measurable),
      inter_eq_right.mpr (hcover c hc)]
  rw [Finset.sum_congr rfl he]
  unfold testedCellDistance
  rw [← Measure.map_finset_sum (by fun_prop)]
  apply Measure.map_mono _ (by fun_prop)
  unfold testedCellPair
  rw [P.restrict_occupiedPaths μ n,Q.restrict_occupiedPaths ν n,
    PlanarFalconer.finite_measure_prod_sum,
    ← Finset.sum_product (P.occupiedPaths μ n) (Q.occupiedPaths ν n)
      (fun c : List (Fin d → Bool) × List (Fin d → Bool) =>
        (μ.restrict (P.descendant c.1).carrier).prod (ν.restrict (Q.descendant c.2).carrier)),
    PlanarFalconer.finite_measure_restrict_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => bot_le)

end Falconer

end OAI
