import OAI.MeasureTheory.Falconer.Measures.PrefixMass

namespace OAI

/-! # Occupied dyadic trees with a common full-measure source core -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def DyadicCube.emptyTreeCells (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : Set (Space d) :=
  ⋃ n ∈ Finset.range (N+1),
    ⋃ p ∈ cubePaths d n \ Q.occupiedPaths μ n, (Q.descendant p).carrier

noncomputable def DyadicCube.occupiedTreeCore (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : Set (Space d) :=
  Q.carrier \ Q.emptyTreeCells μ N

theorem DyadicCube.emptyTreeCells_measurable (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : MeasurableSet (Q.emptyTreeCells μ N) := by
  apply Finset.measurableSet_biUnion
  intro n _
  exact Finset.measurableSet_biUnion _ (fun p _ => (Q.descendant p).measurable)

theorem DyadicCube.emptyTreeCells_null (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : μ (Q.emptyTreeCells μ N) = 0 := by
  apply le_antisymm _ zero_le
  apply (measure_biUnion_finset_le _ _).trans
  apply Finset.sum_nonpos
  intro n _
  apply (measure_biUnion_finset_le _ _).trans
  apply Finset.sum_nonpos
  intro p hp
  obtain ⟨hp,hno⟩ := Finset.mem_sdiff.mp hp
  have hn : ¬ 0 < μ (Q.descendant p).carrier := by
    intro h
    exact hno (Finset.mem_filter.mpr ⟨hp,h⟩)
  exact le_of_not_gt hn

theorem DyadicCube.occupiedTreeCore_measurable (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : MeasurableSet (Q.occupiedTreeCore μ N) :=
  Q.measurable.diff (Q.emptyTreeCells_measurable μ N)

theorem DyadicCube.occupiedTreeCore_full (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) (hroot : μ Q.carrierᶜ = 0) :
    μ (Q.occupiedTreeCore μ N)ᶜ = 0 := by
  classical
  have he : (Q.occupiedTreeCore μ N)ᶜ = Q.carrierᶜ ∪ Q.emptyTreeCells μ N := by
    ext x
    simp only [occupiedTreeCore,mem_compl_iff,mem_sdiff,mem_union]
    tauto
  rw [he]
  apply le_antisymm _ zero_le
  exact (measure_union_le _ _).trans_eq (by rw [hroot,Q.emptyTreeCells_null,zero_add])

theorem DyadicCube.occupiedTreeCore_cover (Q : DyadicCube d)
    (μ : Measure (Space d)) {N n : ℕ} (hn : n ≤ N)
    {x : Space d} (hx : x ∈ Q.occupiedTreeCore μ N) :
    ∃ p ∈ Q.occupiedPaths μ n, x ∈ (Q.descendant p).carrier := by
  classical
  obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth n hx.1
  refine ⟨p,?_,hxp⟩
  by_contra hno
  exact hx.2 (mem_iUnion₂.mpr ⟨n,Finset.mem_range.mpr (by omega),
    mem_iUnion₂.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hp,hno⟩,hxp⟩⟩)

theorem DyadicCube.occupied_parent (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {a b : ℕ} (hab : a ≤ b)
    {p : List (Fin d → Bool)} (hp : p ∈ Q.occupiedPaths μ b) :
    p.take a ∈ Q.occupiedPaths μ a ∧
      (Q.descendant p).carrier ⊆ (Q.descendant (p.take a)).carrier := by
  obtain ⟨hp,hpos⟩ := Finset.mem_filter.mp hp
  have hlen := (mem_cubePaths d b p).mp hp
  have hsub := Regularization.descendant_subset_take Q hQ p a
  refine ⟨Finset.mem_filter.mpr ⟨?_,hpos.trans_le (measure_mono hsub)⟩,hsub⟩
  exact (mem_cubePaths d a _).mpr (by simp only [List.length_take,hlen,Nat.min_eq_left hab])

theorem DyadicCube.occupied_center_bound (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {n : ℕ} {p : List (Fin d → Bool)}
    (hp : p ∈ Q.occupiedPaths μ n) {z : Space d} (hz : z ∈ (Q.descendant p).carrier) :
    ‖z-(Q.descendant p).center‖ ≤ Real.sqrt d*(Q.side/(2:ℝ)^n) := by
  have hlen := (mem_cubePaths d n p).mp (Finset.mem_filter.mp hp).1
  have hb := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hz
    ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p))
  simpa only [dist_eq_norm,Q.descendant_side,hlen] using hb

theorem DyadicCube.occupied_diameter_bound (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {n : ℕ} {p : List (Fin d → Bool)}
    (hp : p ∈ Q.occupiedPaths μ n) {y z : Space d}
    (hy : y ∈ (Q.descendant p).carrier) (hz : z ∈ (Q.descendant p).carrier) :
    ‖y-z‖ ≤ Real.sqrt d*(Q.side/(2:ℝ)^n) := by
  have hlen := (mem_cubePaths d n p).mp (Finset.mem_filter.mp hp).1
  simpa only [dist_eq_norm,Q.descendant_side,hlen] using
    (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hy hz

end Falconer

end OAI
