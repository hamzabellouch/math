import OAI.Geometry.TranslativeCovering.SphericalBlocks

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

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace CellMatching

variable {I : Type u_1} {J : Type u_2} {C : Type u_3} [Fintype I] [Fintype J]

def IsMatching (M : Finset (I × J)) : Prop :=
  (∀ i j k, (i,j) ∈ M → (i,k) ∈ M → j = k) ∧
  (∀ i j k, (i,k) ∈ M → (j,k) ∈ M → i = j)

abbrev Matching (I : Type u_4) (J : Type u_5) [Fintype I] [Fintype J] :=
  {M : Finset (I × J) // IsMatching M}

abbrev Classes (M : Matching I J) := I ⊕ {j : J // ∀ i, (i,j) ∉ M.val}

noncomputable def rightClass (M : Matching I J) (j : J) : Classes M :=
  if h : ∃ i, (i,j) ∈ M.val then Sum.inl h.choose
  else Sum.inr ⟨j, by simpa only [not_exists] using h⟩

lemma rightClass_of_edge (M : Matching I J) {i : I} {j : J}
    (hij : (i,j) ∈ M.val) : rightClass M j = Sum.inl i := by
  have h : ∃ i, (i,j) ∈ M.val := ⟨i, hij⟩
  rw [rightClass, dite_eq_left h]
  congr 1
  exact M.property.2 _ _ _ h.choose_spec hij

lemma rightClass_unmatched (M : Matching I J) (j : J)
    (hj : ∀ i, (i,j) ∉ M.val) : rightClass M j = Sum.inr ⟨j,hj⟩ := by
  have h : ¬ ∃ i, (i,j) ∈ M.val := by simpa only [not_exists] using hj
  simp only [rightClass, dite_eq_right h]

lemma inl_eq_rightClass (M : Matching I J) (i : I) (j : J) :
    Sum.inl i = rightClass M j ↔ (i,j) ∈ M.val := by
  constructor
  · intro h
    unfold rightClass at h
    split_ifs at h with hj
    · have hi := Sum.inl.inj h
      simpa only [hi] using hj.choose_spec
  · intro h
    exact (rightClass_of_edge M h).symm

lemma rightClass_injective (M : Matching I J) : Function.Injective (rightClass M) := by
  intro j k h
  by_cases hj : ∃ i, (i,j) ∈ M.val
  · obtain ⟨i, hi⟩ := hj
    have hk : (i,k) ∈ M.val := (inl_eq_rightClass M i k).mp
      ((rightClass_of_edge M hi).symm.trans h)
    exact M.property.1 _ _ _ hi hk
  · have hj' : ∀ i, (i,j) ∉ M.val := by simpa only [not_exists] using hj
    rw [rightClass_unmatched M j hj'] at h
    unfold rightClass at h
    split_ifs at h with hk
    · exact congrArg Subtype.val (Sum.inr.inj h)

noncomputable def exactMatching (f : I ↪ C) (g : J ↪ C) : Matching I J :=
  ⟨Finset.univ.filter (fun ij => f ij.1 = g ij.2), by
    constructor
    · intro i j k hj hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
      exact g.injective (hj.symm.trans hk)
    · intro i j k hi hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      exact f.injective (hi.trans hj.symm)⟩

@[simp] lemma mem_exactMatching (f : I ↪ C) (g : J ↪ C) (i : I) (j : J) :
    (i,j) ∈ (exactMatching f g).val ↔ f i = g j := by
  simp only [exactMatching, Finset.mem_filter, Finset.mem_univ, true_and]

abbrev ExactPair (M : Matching I J) (C : Type u_6) :=
  {fg : (I ↪ C) × (J ↪ C) // ∀ i j, fg.1 i = fg.2 j ↔ (i,j) ∈ M.val}

noncomputable def expand (M : Matching I J) (q : Classes M ↪ C) : ExactPair M C :=
  ⟨(⟨fun i => q (Sum.inl i), q.injective.comp Sum.inl_injective⟩,
    ⟨fun j => q (rightClass M j), q.injective.comp (rightClass_injective M)⟩), by
    intro i j
    exact q.injective.eq_iff.trans (inl_eq_rightClass M i j)⟩

noncomputable def collapse (M : Matching I J) (fg : ExactPair M C) : Classes M ↪ C :=
  ⟨Sum.elim fg.val.1 (fun j => fg.val.2 j.val), by
    rintro (i | j) (i' | j') h
    · exact congrArg Sum.inl (fg.val.1.injective h)
    · exact False.elim (j'.property i ((fg.property i j').mp h))
    · exact False.elim (j.property i' ((fg.property i' j).mp h.symm))
    · exact congrArg Sum.inr (Subtype.ext (fg.val.2.injective h))⟩

lemma collapse_right (M : Matching I J) (fg : ExactPair M C) (j : J) :
    collapse M fg (rightClass M j) = fg.val.2 j := by
  unfold rightClass
  split_ifs with h
  · exact (fg.property h.choose j).mpr h.choose_spec
  · rfl

noncomputable def diagramEquiv (M : Matching I J) :
    (Classes M ↪ C) ≃ ExactPair M C where
  toFun := expand M
  invFun := collapse M
  left_inv q := by
    ext (i | j)
    · rfl
    · change q (rightClass M j) = q (Sum.inr j)
      rw [rightClass_unmatched M j j.property]
  right_inv fg := by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      rfl
    · ext j
      exact collapse_right M fg j

def classIncidence (M : Matching I J) (A : I → C → Prop) (B : J → C → Prop) :
    Classes M → C → Prop :=
  Sum.elim (fun i c => A i c ∧ ∀ j, (i,j) ∈ M.val → B j c)
    (fun j c => B j.val c)

lemma incidence_equiv (M : Matching I J) (A : I → C → Prop) (B : J → C → Prop)
    (q : Classes M ↪ C) :
    (∀ v, classIncidence M A B v (q v)) ↔
      (∀ i, A i ((expand M q).val.1 i)) ∧ (∀ j, B j ((expand M q).val.2 j)) := by
  constructor
  · intro h
    constructor
    · intro i
      exact (h (Sum.inl i)).1
    · intro j
      by_cases hj : ∃ i, (i,j) ∈ M.val
      · obtain ⟨i, hi⟩ := hj
        have hb := (h (Sum.inl i)).2 j hi
        change B j (q (rightClass M j))
        rwa [rightClass_of_edge M hi]
      · have hj' : ∀ i, (i,j) ∉ M.val := by simpa only [not_exists] using hj
        change B j (q (rightClass M j))
        rw [rightClass_unmatched M j hj']
        exact h (Sum.inr ⟨j,hj'⟩)
  · rintro ⟨hA,hB⟩ (i | j)
    · refine ⟨hA i, ?_⟩
      intro j hij
      have hb := hB j
      change B j (q (rightClass M j)) at hb
      rwa [rightClass_of_edge M hij] at hb
    · have hb := hB j
      change B j (q (rightClass M j)) at hb
      rwa [rightClass_unmatched M j j.property] at hb

variable [Fintype C]

noncomputable def support (f : I ↪ C) : Finset C := Finset.univ.image f

noncomputable def jointWeight (p : C → ℝ) (f : I ↪ C) (g : J ↪ C) : ℝ :=
  ∏ c ∈ support f ∪ support g, p c

omit [Fintype C] in
lemma expansion_support (M : Matching I J) (q : Classes M ↪ C) :
    support (expand M q).val.1 ∪ support (expand M q).val.2 = support q := by
  ext c
  simp only [support, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨i,hi⟩ | ⟨j,hj⟩)
    · exact ⟨Sum.inl i, hi⟩
    · exact ⟨rightClass M j, hj⟩
  · rintro ⟨v,hv⟩
    rcases v with i | j
    · exact Or.inl ⟨i,hv⟩
    · right
      refine ⟨j, ?_⟩
      change q (rightClass M j) = c
      simpa only [rightClass_unmatched M j j.property] using hv

omit [Fintype C] in
lemma expansion_weight (M : Matching I J) (q : Classes M ↪ C) (p : C → ℝ) :
    jointWeight p (expand M q).val.1 (expand M q).val.2 = ∏ v, p (q v) := by
  rw [jointWeight, expansion_support, support, Finset.prod_image]
  exact q.injective.injOn

noncomputable def pairWeight (A : I → C → Prop) (B : J → C → Prop) (p : C → ℝ)
    (fg : (I ↪ C) × (J ↪ C)) : ℝ :=
  if (∀ i, A i (fg.1 i)) ∧ (∀ j, B j (fg.2 j)) then jointWeight p fg.1 fg.2 else 0

lemma diagram_sum (M : Matching I J) (A : I → C → Prop) (B : J → C → Prop)
    (p : C → ℝ) :
    (∑ fg : ExactPair M C, pairWeight A B p fg.val) =
      ∑ q : Classes M ↪ C, if ∀ v, classIncidence M A B v (q v)
        then ∏ v, p (q v) else 0 := by
  rw [← (diagramEquiv M).sum_comp (fun fg => pairWeight A B p fg.val)]
  apply Finset.sum_congr rfl
  intro q _
  change pairWeight A B p (expand M q).val = _
  simp only [pairWeight, ← incidence_equiv, expansion_weight]

omit [Fintype C] in

lemma support_inter_nonempty_iff (f : I ↪ C) (g : J ↪ C) :
    (support f ∩ support g).Nonempty ↔ (exactMatching f g).val.Nonempty := by
  simp only [Finset.nonempty_iff_ne_empty]
  constructor
  · contrapose!
    intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    rcases Finset.mem_inter.mp hc with ⟨hf,hg⟩
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hf
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hg
    have hm : (i,j) ∈ (exactMatching f g).val :=
      (mem_exactMatching f g i j).mpr (hi.trans hj.symm)
    simp only [h, Finset.notMem_empty] at hm
  · contrapose!
    intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨i,j⟩ hm
    have he := (mem_exactMatching f g i j).mp hm
    have hc : f i ∈ support f ∩ support g := Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
       Finset.mem_image.mpr ⟨j, Finset.mem_univ _, he.symm⟩⟩
    simp only [h, Finset.notMem_empty] at hc

noncomputable def allDiagramsEquiv :
    ((I ↪ C) × (J ↪ C)) ≃ Σ M : Matching I J, ExactPair M C where
  toFun fg := ⟨exactMatching fg.1 fg.2, ⟨fg, fun i j => (mem_exactMatching _ _ i j).symm⟩⟩
  invFun mq := mq.2.val
  left_inv fg := rfl
  right_inv mq := by
    rcases mq with ⟨M, fg, hfg⟩
    have hM : exactMatching fg.1 fg.2 = M := by
      apply Subtype.ext
      ext ij
      exact (mem_exactMatching _ _ ij.1 ij.2).trans (hfg ij.1 ij.2)
    cases hM
    rfl

lemma all_diagram_sum (A : I → C → Prop) (B : J → C → Prop) (p : C → ℝ) :
    (∑ fg : (I ↪ C) × (J ↪ C), pairWeight A B p fg) =
      ∑ M : Matching I J, ∑ q : Classes M ↪ C,
        if ∀ v, classIncidence M A B v (q v) then ∏ v, p (q v) else 0 := by
  have h := (allDiagramsEquiv (I := I) (J := J) (C := C)).sum_comp
    (fun mq => pairWeight A B p mq.2.val)
  change (∑ fg, pairWeight A B p fg) = _ at h
  rw [h, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro M _
  exact diagram_sum M A B p

omit [Fintype C] in
lemma matching_eq (M : Matching I J) (fg : ExactPair M C) :
    exactMatching fg.val.1 fg.val.2 = M := by
  apply Subtype.ext
  ext ij
  exact (mem_exactMatching _ _ ij.1 ij.2).trans (fg.property ij.1 ij.2)

lemma dependency_diagram_sum (A : I → C → Prop) (B : J → C → Prop) (p : C → ℝ) :
    (∑ fg : (I ↪ C) × (J ↪ C),
      if (support fg.1 ∩ support fg.2).Nonempty then pairWeight A B p fg else 0) =
      ∑ M : Matching I J, if M.val.Nonempty then
        ∑ q : Classes M ↪ C,
          if ∀ v, classIncidence M A B v (q v) then ∏ v, p (q v) else 0
      else 0 := by
  simp only [support_inter_nonempty_iff]
  have h := (allDiagramsEquiv (I := I) (J := J) (C := C)).sum_comp
    (fun mq => if (exactMatching mq.2.val.1 mq.2.val.2).val.Nonempty
      then pairWeight A B p mq.2.val else 0)
  change (∑ fg, if (exactMatching fg.1 fg.2).val.Nonempty
    then pairWeight A B p fg else 0) = _ at h
  rw [h, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro M _
  simp only [matching_eq]
  by_cases hm : M.val.Nonempty
  · simp only [ite_eq_left hm]
    exact diagram_sum M A B p
  · simp only [ite_eq_right hm, Finset.sum_const_zero]

end CellMatching

end OAI
