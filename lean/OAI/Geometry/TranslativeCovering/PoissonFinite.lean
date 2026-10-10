import OAI.Geometry.TranslativeCovering.JansonSampling

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

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace PoissonFinite
open Set MeasureTheory ProbabilityTheory PoissonConfig PoissonMeasureCells CellMatching PoissonDiagrams
open scoped Classical BigOperators
variable {Ω : Type u_1} {A : Type u_2} {C : Type u_3} [MeasurableSpace Ω] [Fintype A] [Fintype C]
variable {I : A → Type u_4} [∀ a, Fintype (I a)]

abbrev Assignment (I : A → Type u_5) (C : Type u_6) := Σ a, I a ↪ C

noncomputable def valid (P : Partition Ω C) (E : ∀ a, I a → Set Ω)
    (f : Assignment I C) : Prop := ∀ i, P.cell (f.2 i) ⊆ E f.1 i

noncomputable def validAssignments (P : Partition Ω C) (E : ∀ a, I a → Set Ω) :
    Finset (Assignment I C) := Finset.univ.filter (valid P E)

noncomputable def assignmentSupport (f : Assignment I C) : Finset C := support f.2

lemma assignment_mean (P : Partition Ω C) (E : ∀ a, I a → Set Ω) (p : C → ℝ) :
    FiniteJanson.mean p assignmentSupport (validAssignments P E) =
      ∑ a, CellCounts.injectiveSum (CellCounts.slotWeight (fun i c => P.cell c ⊆ E a i) p) := by
  rw [FiniteJanson.mean, validAssignments, Finset.sum_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [CellCounts.injectiveSum_slot_eq]
  apply Finset.sum_congr rfl
  intro f _
  dsimp only [valid]
  rw [FiniteJanson.prob_occurs]
  congr 1
  exact Finset.prod_image f.injective.injOn

lemma assignment_depSum (P : Partition Ω C) (E : ∀ a, I a → Set Ω) (p : C → ℝ) :
    FiniteJanson.depSum p assignmentSupport (validAssignments P E) =
      ∑ a, ∑ b, ∑ fg : (I a ↪ C) × (I b ↪ C),
        if (support fg.1 ∩ support fg.2).Nonempty then
          pairWeight (fun i c => P.cell c ⊆ E a i) (fun j c => P.cell c ⊆ E b j) p fg else 0 := by
  have he : FiniteJanson.depSum p assignmentSupport (validAssignments P E) =
      ∑ f : Assignment I C, ∑ g : Assignment I C,
        if valid P E f ∧ valid P E g then
          if (support f.2 ∩ support g.2).Nonempty then jointWeight p f.2 g.2 else 0 else 0 := by
    rw [FiniteJanson.depSum, validAssignments, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : valid P E f
    · rw [ite_eq_left hf, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : valid P E g
      · simp only [hg, hf, and_self, ite_true]
        rw [← FiniteJanson.occurs_union, FiniteJanson.prob_occurs]
        change (if Disjoint (support f.2) (support g.2) then 0 else jointWeight p f.2 g.2) = _
        by_cases hd : Disjoint (support f.2) (support g.2)
        · have hn : ¬ (support f.2 ∩ support g.2).Nonempty := by
            rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
            exact Finset.not_nonempty_empty
          rw [ite_eq_left hd, ite_eq_right hn]
        · have hn : (support f.2 ∩ support g.2).Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr (fun h => hd (Finset.disjoint_iff_inter_eq_empty.mpr h))
          rw [ite_eq_right hd, ite_eq_left hn]
      · rw [ite_eq_right hg, ite_eq_right (by simp only [hg, and_false, not_false_eq_true])]
    · rw [ite_eq_right hf]
      simp only [hf, false_and, ↓reduceIte, Finset.sum_const_zero]
  rw [he, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [Fintype.sum_sigma]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro g _
  dsimp only [valid, pairWeight]
  by_cases h : (∀ i, P.cell (f i) ⊆ E a i) ∧ ∀ j, P.cell (g j) ⊆ E b j
  · simp [h]
  · simp [h]

omit [Fintype A] in

lemma witness_of_cell_occupation (P : Partition Ω C) (E : ∀ a, I a → Set Ω)
    (f : Assignment I C) (hf : valid P E f) (x : Config Ω)
    (hx : ∀ c ∈ assignmentSupport f, occupied (P.cell c) x = true) :
    0 < witnessCount (E f.1) x := by
  have hi (i : I f.1) : ∃ j : Fin x.1, x.2.val j ∈ P.cell (f.2 i) := by
    have h := hx (f.2 i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    simp only [occupied, decide_eq_true_eq, count, Finset.card_pos, Finset.filter_nonempty_iff,
      Finset.mem_univ, true_and] at h
    exact h
  choose g hg using hi
  have hginj : Function.Injective g := by
    intro i j hij
    apply f.2.injective
    by_contra hc
    exact Set.disjoint_left.mp (P.disjoint hc) (hg i) (by simpa only [hij] using hg j)
  let w : I f.1 ↪ Fin x.1 := ⟨g,hginj⟩
  apply Finset.card_pos.mpr
  refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro i
  exact hf i (hg i)

theorem finite_cell_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : Measure (Config Ω)) [IsProbabilityMeasure P] (hP : HasVoidLaw μ P)
    [∀ a, Nonempty (I a)] (cells : Partition Ω C) (E : ∀ a, I a → Set Ω)
    (hm : 0 < ∑ a, Q μ cells (E a)) :
    (∑ a, Q μ cells (E a)) ≤
      (∑ a, ∑ b, ∑ M : Matching (I a) (I b), if M.val.Nonempty then
        Q μ cells (classSet M (E a) (E b)) else 0) ∧
    P.real {x | ∀ a, witnessCount (E a) x = 0} ≤ Real.exp
      (-(∑ a, Q μ cells (E a))^2 /
        (2 * (∑ a, ∑ b, ∑ M : Matching (I a) (I b), if M.val.Nonempty then
          Q μ cells (classSet M (E a) (E b)) else 0))) := by
  let p : C → ℝ := fun c => 1 - Real.exp (-μ.real (cells.cell c))
  have hp : FiniteJanson.successProb P (fun c => occupied (cells.cell c)) = p := by
    funext c
    exact occupied_prob_of_void hP (cells.measurable c)
  have hmean : FiniteJanson.mean p assignmentSupport (validAssignments cells E) =
      ∑ a, Q μ cells (E a) := assignment_mean cells E p
  have hdep : FiniteJanson.depSum p assignmentSupport (validAssignments cells E) =
      ∑ a, ∑ b, ∑ M : Matching (I a) (I b), if M.val.Nonempty then
        Q μ cells (classSet M (E a) (E b)) else 0 := by
    rw [assignment_depSum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact dependency_eq_sum_Q μ cells (E a) (E b)
  have hj := FiniteJanson.janson_of_iIndepFun
    (fun c => measurable_occupied (cells.measurable c))
    (occupied_independent_of_void hP cells.cell cells.measurable cells.disjoint)
    assignmentSupport (validAssignments cells E)
    (fun f _ => by
      obtain ⟨i⟩ := (inferInstance : Nonempty (I f.1))
      exact ⟨f.2 i, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
    (by rw [hp,hmean]; exact hm)
  rw [hp,hmean,hdep] at hj
  refine ⟨hj.1, (measureReal_mono (μ := P) ?_).trans hj.2⟩
  intro x hx f hf hocc
  have hvalid : valid cells E f := (Finset.mem_filter.mp hf).2
  have hpos := witness_of_cell_occupation cells E f hvalid x hocc
  rw [hx f.1] at hpos
  exact (lt_irrefl 0 hpos)

end PoissonFinite

end OAI
