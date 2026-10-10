import Mathlib

namespace OAI

universe uX uIndex

noncomputable section

open Set MeasureTheory

namespace Problem356.FiniteCells

/-- The exact label of a point in a disjoint family; points outside all cells
are assigned `none`, without choosing an arbitrary distinguished cell. -/
def cellLabel {X : Type uX} {ι : Type uIndex} (A : ι → Set X) (x : X) : Option ι :=
  by
    classical
    exact if h : ∃ i, x ∈ A i then some (Classical.choose h) else none

lemma cellLabel_eq_some_iff {X : Type uX} {ι : Type uIndex} {A : ι → Set X}
    (hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) (x : X) (i : ι) :
    cellLabel A x = some i ↔ x ∈ A i := by
  classical
  unfold cellLabel
  split_ifs with h
  · constructor
    · intro hi
      have hi' := Option.some.inj hi
      rw [← hi']
      exact Classical.choose_spec h
    · intro hx
      congr 1
      by_contra hne
      exact Set.disjoint_left.mp (hDisjoint hne) (Classical.choose_spec h) hx
  · have hi : x ∉ A i := fun hx => h ⟨i, hx⟩
    simp [hi]

lemma cellLabel_eq_none_iff {X : Type uX} {ι : Type uIndex} (A : ι → Set X) (x : X) :
    cellLabel A x = none ↔ x ∉ ⋃ i, A i := by
  classical
  by_cases h : ∃ i, x ∈ A i
  · simp only [cellLabel, dite_eq_left h, reduceCtorEq, false_iff, not_not]
    exact mem_iUnion.mpr h
  · simp only [cellLabel, dite_eq_right h, true_iff]
    exact fun hx => h (mem_iUnion.mp hx)

lemma cellLabel_fiber_some {X : Type uX} {ι : Type uIndex} {A : ι → Set X}
    (hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) (i : ι) :
    cellLabel A ⁻¹' {some i} = A i := by
  ext x
  exact cellLabel_eq_some_iff hDisjoint x i

lemma cellLabel_fiber_none {X : Type uX} {ι : Type uIndex} (A : ι → Set X) :
    cellLabel A ⁻¹' {none} = (⋃ i, A i)ᶜ := by
  ext x
  exact cellLabel_eq_none_iff A x

lemma measurable_cellLabel {X : Type uX} {ι : Type uIndex} [MeasurableSpace X]
    [MeasurableSpace (Option ι)] [Countable ι] {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i))
    (hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) :
    Measurable (cellLabel A) := by
  apply measurable_to_countable'
  intro i
  cases i with
  | none =>
      rw [cellLabel_fiber_none]
      exact (MeasurableSet.iUnion hA).compl
  | some i =>
      rw [cellLabel_fiber_some hDisjoint]
      exact hA i

/-- Equal source cell masses give equal laws of the exact label, provided
both measures are concentrated on the union of the cells. -/
lemma map_cellLabel_eq_of_cell_masses {X : Type uX} {ι : Type uIndex} [MeasurableSpace X]
    [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)] [Countable ι]
    {μ ν : Measure X} {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i))
    (hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hμ : μ (⋃ i, A i)ᶜ = 0) (hν : ν (⋃ i, A i)ᶜ = 0)
    (hmass : ∀ i, μ (A i) = ν (A i)) :
    Measure.map (cellLabel A) μ = Measure.map (cellLabel A) ν := by
  have hm := measurable_cellLabel hA hDisjoint
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.map_apply hm (measurableSet_singleton i),
    Measure.map_apply hm (measurableSet_singleton i)]
  cases i with
  | none => simp only [cellLabel_fiber_none, hμ, hν]
  | some i => simpa only [cellLabel_fiber_some hDisjoint] using hmass i

end Problem356.FiniteCells

end

end OAI
