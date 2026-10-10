import OAI.Geometry.TranslativeCovering.PoissonFinite

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1 u_2

namespace PoissonCells

variable {Ω : Type u_1} {J : Type u_2} [MeasurableSpace Ω] [Fintype J]

noncomputable def atom (E : J → Set Ω) (b : J → Bool) : Set Ω :=
  {x | ∀ j, decide (x ∈ E j) = b j}

lemma atom_measurable (E : J → Set Ω) (hE : ∀ j, MeasurableSet (E j)) (b : J → Bool) :
    MeasurableSet (atom E b) := by
  classical
  simp only [atom, ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  cases hb : b j
  · convert! (hE j).compl using 1
    ext x
    simp only [mem_ofPred_eq, decide_eq_false_iff_not, mem_compl_iff]
  · convert! hE j using 1
    ext x
    simp only [mem_ofPred_eq, decide_eq_true_eq]

omit [MeasurableSpace Ω] [Fintype J] in
lemma atom_disjoint (E : J → Set Ω) : Pairwise (fun b c => Disjoint (atom E b) (atom E c)) := by
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro x hxb hxc
  apply hbc
  funext j
  exact (hxb j).symm.trans (hxc j)

omit [MeasurableSpace Ω] [Fintype J] in
lemma atom_cover (E : J → Set Ω) : (⋃ b, atom E b) = univ := by
  classical
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨fun j => decide (x ∈ E j), fun _ => rfl⟩

omit [MeasurableSpace Ω] [Fintype J] in
lemma atom_respects (E : J → Set Ω) (b : J → Bool) (j : J) :
    atom E b ⊆ E j ∨ Disjoint (atom E b) (E j) := by
  classical
  cases hb : b j
  · right
    apply Set.disjoint_left.mpr
    intro x hx hxj
    have := hx j
    simp [hb, hxj] at this
  · left
    intro x hx
    have := hx j
    simpa [hb] using this

omit [Fintype J] in

lemma exists_small_cover [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [NullSingletonClass μ] {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ s : Finset (Set Ω), (∀ U ∈ s, MeasurableSet U ∧ μ U < δ) ∧
      (⋃ U ∈ s, U) = univ := by
  classical
  let := upgradeStandardBorel Ω
  obtain ⟨K, -, hK, hKμ⟩ := MeasurableSet.univ.exists_isCompact_sdiff_lt
    (μ := μ) (measure_ne_top μ univ) (ne_of_gt hδ)
  have hx : ∀ x : Ω, ∃ U : Set Ω, x ∈ U ∧ IsOpen U ∧ μ U < δ := by
    intro x
    obtain ⟨U, hxU, hoU, hμU⟩ := ({x} : Set Ω).exists_isOpen_lt_of_lt
      (μ := μ) δ (by simpa using hδ)
    exact ⟨U, hxU (mem_singleton x), hoU, hμU⟩
  choose U hxU hoU hμU using hx
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hoU (by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨insert Kᶜ (t.image U), ?_, ?_⟩
  · intro V hV
    rcases Finset.mem_insert.mp hV with rfl | hV
    · exact ⟨hK.isClosed.measurableSet.compl, by simpa only [Set.sdiff_eq_compl_inter, Set.inter_univ] using hKμ⟩
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hV
      exact ⟨(hoU x).measurableSet, hμU x⟩
  · apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (ht hx)
      exact mem_iUnion₂.mpr ⟨U z, Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨z, hz, rfl⟩), hxz⟩
    · exact mem_iUnion₂.mpr ⟨Kᶜ, Finset.mem_insert_self _ _, hx⟩

lemma exists_fine_partition [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [NullSingletonClass μ] (E : J → Set Ω)
    (hE : ∀ j, MeasurableSet (E j)) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ s : Finset (Set Ω),
      (∀ C ∈ s, MeasurableSet C ∧ μ C < δ) ∧
      (s : Set (Set Ω)).PairwiseDisjoint id ∧
      (⋃ C ∈ s, C) = univ ∧
      ∀ j C, C ∈ s → C ⊆ E j ∨ Disjoint C (E j) := by
  classical
  obtain ⟨t, ht, htcover⟩ := exists_small_cover μ hδ
  let A : J ⊕ ↥t → Set Ω := Sum.elim E (fun U => U.val)
  have hA : ∀ i, MeasurableSet (A i) := by
    intro i
    rcases i with j | U
    · exact hE j
    · exact (ht U.val U.property).1
  let s := Finset.univ.image (atom A)
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hC
    refine ⟨atom_measurable A hA b, ?_⟩
    by_cases hne : (atom A b).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hxc : x ∈ ⋃ U ∈ t, U := by simp only [htcover, mem_univ]
      obtain ⟨U, hU, hxU⟩ := mem_iUnion₂.mp hxc
      have hs : atom A b ⊆ U := by
        intro y hy
        have hb := hx (Sum.inr ⟨U, hU⟩)
        have hyb := hy (Sum.inr ⟨U, hU⟩)
        apply of_decide_eq_true
        calc
          decide (y ∈ U) = decide (x ∈ U) := hyb.trans hb.symm
          _ = true := by simp only [hxU, decide_true]
      exact (measure_mono hs).trans_lt (ht U hU).2
    · simp only [Set.not_nonempty_iff_eq_empty] at hne
      simpa only [hne, measure_empty] using hδ
  · intro C hC D hD hCD
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hD
    exact atom_disjoint A (fun h => hCD (congrArg (atom A) h))
  · apply eq_univ_of_forall
    intro x
    obtain ⟨b, hxb⟩ := mem_iUnion.mp (show x ∈ ⋃ b, atom A b by rw [atom_cover]; trivial)
    exact mem_iUnion₂.mpr ⟨atom A b, Finset.mem_image.mpr
      ⟨b, Finset.mem_univ _, rfl⟩, hxb⟩
  · intro j C hC
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hC
    exact atom_respects A b (Sum.inl j)

end PoissonCells

end OAI
