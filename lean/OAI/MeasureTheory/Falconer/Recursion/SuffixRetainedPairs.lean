import OAI.MeasureTheory.Falconer.Radial.ProjectionCellPartition
import OAI.MeasureTheory.Falconer.Measures.FiniteMeasureProducts
import OAI.MeasureTheory.Falconer.Estimates.PositiveDistancePushforward

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

noncomputable def suffixRectangles (d : PositiveDistanceData) (p : ℕ) : Finset (CellPath × CellPath) :=
  (projectionTestCells d.Q d.ρ d.a p d.X).product (projectionTestCells d.Q d.ρ d.a p d.Y)

noncomputable def suffixRetained (d : PositiveDistanceData) (p : ℕ) : Finset (CellPath × CellPath) := by
  classical
  exact (d.suffixRectangles p).filter fun c =>
    ∃ x ∈ (d.Q.descendant c.1).carrier, ∃ y ∈ (d.Q.descendant c.2).carrier, (x,y) ∈ d.good

abbrev suffixData (d : PositiveDistanceData) (c : CellPath × CellPath) : PositiveDistanceData :=
  {d with X := c.1,Y := c.2}

noncomputable def suffixFullDistance (d : PositiveDistanceData) (c : CellPath × CellPath) : Measure ℝ :=
  Measure.map (fun z : Plane × Plane => dist z.1 z.2) (d.suffixData c).cellPair

instance suffixFullDistance_finite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (c : CellPath × CellPath) : IsFiniteMeasure (d.suffixFullDistance c) := by
  unfold suffixFullDistance
  infer_instance

theorem suffix_retained_spec (d : PositiveDistanceData) {p : ℕ} {c : CellPath × CellPath}
    (hc : c ∈ d.suffixRetained p) :
    c.1.length = p ∧ c.2.length = p ∧ c.1.take d.a = d.X ∧ c.2.take d.a = d.Y ∧
      ∃ x ∈ (d.Q.descendant c.1).carrier, ∃ y ∈ (d.Q.descendant c.2).carrier, (x,y) ∈ d.good := by
  classical
  obtain ⟨hc,hw⟩ := Finset.mem_filter.mp hc
  obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hc
  exact ⟨(mem_dyadicPaths _ _).mp (Finset.mem_filter.mp h₁).1,
    (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp h₂).1,
    (Finset.mem_filter.mp h₁).2.2,(Finset.mem_filter.mp h₂).2.2,hw⟩

theorem cellPair_split_suffix (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    d.cellPair = ∑ c ∈ d.suffixRectangles p, (d.suffixData c).cellPair := by
  change (d.ρ.restrict (d.Q.descendant d.X).carrier).prod
    (d.ρ.restrict (d.Q.descendant d.Y).carrier) = _
  rw [projection_measure_split d.Q hQ d.ρ hap hX,
    projection_measure_split d.Q hQ d.ρ hap hY,finite_measure_prod_sum]
  simp only [suffixRectangles,cellPair]
  exact (Finset.sum_product (projectionTestCells d.Q d.ρ d.a p d.X)
    (projectionTestCells d.Q d.ρ d.a p d.Y)
    (fun c : CellPath × CellPath => (d.ρ.restrict (d.Q.descendant c.1).carrier).prod
      (d.ρ.restrict (d.Q.descendant c.2).carrier))).symm

theorem pair_zero_of_no_witness (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] (c : CellPath × CellPath)
    (hw : ¬ ∃ x ∈ (d.Q.descendant c.1).carrier,
      ∃ y ∈ (d.Q.descendant c.2).carrier, (x,y) ∈ d.good) : (d.suffixData c).pair = 0 := by
  apply Measure.restrict_eq_zero.mpr
  change ((d.ρ.restrict (d.Q.descendant c.1).carrier).prod
    (d.ρ.restrict (d.Q.descendant c.2).carrier)) d.good = 0
  rw [Measure.prod_restrict,Measure.restrict_apply d.measurable_good]
  have he : d.good ∩ ((d.Q.descendant c.1).carrier ×ˢ (d.Q.descendant c.2).carrier) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hw ⟨z.1,hz.2.1,z.2,hz.2.2,hz.1⟩
  rw [he,measure_empty]

theorem pair_split_retained (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    d.pair = ∑ c ∈ d.suffixRetained p, (d.suffixData c).pair := by
  classical
  rw [pair,d.cellPair_split_suffix hQ hap hX hY,finite_measure_restrict_sum]
  change (∑ c ∈ d.suffixRectangles p, (d.suffixData c).pair) = _
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c hc hn
  apply d.pair_zero_of_no_witness c
  intro hw
  exact hn (Finset.mem_filter.mpr ⟨hc,hw⟩)

theorem distance_split_retained (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    d.distance = ∑ c ∈ d.suffixRetained p, (d.suffixData c).distance := by
  rw [distance,d.pair_split_retained hQ hap hX hY,Measure.map_finset_sum (by fun_prop)]
  rfl

end PositiveDistanceData

end PlanarFalconer

end OAI
