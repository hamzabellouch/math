import OAI.NumberTheory.DukePrimeDegree.Geometry.RowSingleBox

namespace OAI

/-!
# Coordinate measures of compatible row and root boxes

The actual coordinate measure of the one-root box is the coordinate
change of the actual row-box measure. Consequently the abstract nested
conditional compatibility applies to these restricted ambient measures.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma RowRootBox.coordinateMeasure_apply {n : ℕ} {i k : Fin n}
    (B : RowRootBox i k) (μ : Measure (X n)) {S : Set (RowRootSlice i k × RowTime i)}
    (hS : MeasurableSet S) :
    B.coordinateMeasure μ S = μ (rowQuotientParametrization i k '' (S ∩ B.domain)) := by
  rw [RowRootBox.coordinateMeasure, Measure.map_apply measurable_subtype_coe hS,
    B.embedding.measurableEmbedding.comap_apply]
  congr 1
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.val, ⟨hz, z.prop⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hzd⟩, rfl⟩
    exact ⟨⟨z, hzd⟩, hz, rfl⟩

theorem singleRootBox_coordinateMeasure {n : ℕ} {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (B : RowRootBox i k) {R : ℝ} (hR : 0 < R) (hT : B.time = rowCube i R)
    (μ : Measure (X n)) :
    (B.singleRootBox hij hR hT).coordinateMeasure μ =
      (B.coordinateMeasure μ).map (rowToSingleHomeomorph hij k) := by
  let E := rowToSingleHomeomorph hij k
  have hdom (w : RowRootSlice i k × RowTime i) :
      w ∈ B.domain ↔ E w ∈ (B.singleRootBox hij hR hT).domain :=
    rowToSingle_domain hij B hR hT w
  ext S hS
  rw [RootBox.coordinateMeasure_apply _ μ hS, Measure.map_apply E.continuous.measurable hS,
    B.coordinateMeasure_apply μ (E.continuous.measurable hS)]
  congr 1
  ext x
  constructor
  · rintro ⟨z, ⟨hzS, hzD⟩, hz⟩
    refine ⟨E.symm z, ⟨?_, (hdom _).mpr ?_⟩, ?_⟩
    · simpa only [Set.mem_preimage, E.apply_symm_apply] using hzS
    · simpa only [E.apply_symm_apply] using hzD
    · rw [← rowToSingleHomeomorph_param hij k]
      simpa only [E, Homeomorph.apply_symm_apply] using hz
  · rintro ⟨w, ⟨hwS, hwD⟩, hw⟩
    exact ⟨E w, ⟨hwS, (hdom _).mp hwD⟩,
      (rowToSingleHomeomorph_param hij k w).trans hw⟩

lemma rowSingleMeasure_eq_map {n : ℕ} {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (ρ : Measure (RowRootSlice i k × RowTime i)) :
    rowSingleMeasure hij ρ = ρ.map (rowToSingleHomeomorph hij k) := by
  unfold rowSingleMeasure rowSplitMeasure
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem rowBox_root_conditional_compatibility {n : ℕ} {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (B : RowRootBox i k) {R : ℝ} (hR : 0 < R) (hT : B.time = rowCube i R)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(rowSplitMeasure hij (B.coordinateMeasure μ)).fst,
      ∀ᵐ w ∂((rowSplitMeasure hij (B.coordinateMeasure μ)).condKernel s).fst,
        (B.singleRootBox hij hR hT).conditionalKernel μ
            ((rowReducedHomeomorph hij k).symm (s, w)) =
          ((rowSplitMeasure hij (B.coordinateMeasure μ)).condKernel s).condKernel w := by
  have h := row_conditional_compatibility hij (B.coordinateMeasure μ)
  have he : rowSingleMeasure hij (B.coordinateMeasure μ) =
      (B.singleRootBox hij hR hT).coordinateMeasure μ :=
    (rowSingleMeasure_eq_map hij _).trans (singleRootBox_coordinateMeasure hij B hR hT μ).symm
  simpa only [RootBox.conditionalKernel, he] using h

end DukePrimeDegree

end

end OAI
