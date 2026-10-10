import Mathlib
import OAI.GroupTheory.FiniteType.TwistedBrinPrefix

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

noncomputable def translateEquiv (g : localGroup ρ) (B : Basis ρ) : B ≃ translate ρ g B := by
  classical
  let f : B → translate ρ g B := fun b =>
    ⟨GermBrick.groupEquiv ρ g b.val,Finset.mem_map.mpr ⟨b.val,b.property,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro b c he
    apply Subtype.ext
    exact (GermBrick.groupEquiv ρ g).injective (congrArg Subtype.val he)
  · intro c
    obtain ⟨b,hb,hbc⟩ := Finset.mem_map.mp c.property
    exact ⟨⟨b,hb⟩,Subtype.ext hbc⟩

@[simp] lemma translateEquiv_val (g : localGroup ρ) (B : Basis ρ) (b : B) :
    (translateEquiv ρ g B b).val = GermBrick.groupEquiv ρ g b.val := rfl

lemma translate_chart_gauge (g : localGroup ρ) (B : Basis ρ) (b : B) :
    ∃ a : A, chart ρ (translate ρ g B) (translateEquiv ρ g B b) =
      LocalEmbedding.comp ρ (LocalEmbedding.comp ρ (LocalEmbedding.ofGroup ρ g)
        (chart ρ B b)) (LocalEmbedding.global ρ a) := by
  apply (GermBrick.mk_eq_iff ρ _ _).mp
  change GermBrick.mk ρ (GermBrick.representative ρ _) =
    GermBrick.map ρ (LocalEmbedding.ofGroup ρ g)
      (GermBrick.mk ρ (GermBrick.representative ρ b.val))
  simp only [GermBrick.mk_representative]
  rfl

lemma translate_cutRefines (g : localGroup ρ) {B C : Basis ρ}
    (hBC : CutRefines ρ B C) : CutRefines ρ (translate ρ g B) (translate ρ g C) := by
  classical
  obtain ⟨F⟩ := hBC
  choose a ha using translate_chart_gauge ρ g B
  let e := translateEquiv ρ g B
  let P := fun c : translate ρ g B =>
    Pattern.relabel (ρ (a (e.symm c))⁻¹) (F.pattern (e.symm c))
  apply Nonempty.intro
  apply Forest.of_mem ρ P
  rintro ⟨c,j⟩
  let b := e.symm c
  have hroot : chart ρ (translate ρ g B) c =
      LocalEmbedding.comp ρ (LocalEmbedding.comp ρ (LocalEmbedding.ofGroup ρ g)
        (chart ρ B b)) (LocalEmbedding.global ρ (a b)) := by
    have hh := ha b
    change chart ρ (translate ρ g B) (e (e.symm c)) = _ at hh
    rwa [e.apply_symm_apply] at hh
  obtain ⟨k,rfl⟩ := (Pattern.relabelLeaves (ρ (a b)⁻¹) (F.pattern b)).surjective j
  change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ (translate ρ g B) c)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix
      (Pattern.relabel (ρ (a b)⁻¹) (F.pattern b))
        (Pattern.relabelLeaves (ρ (a b)⁻¹) (F.pattern b) k)))) ∈ _
  rw [Pattern.relabel_prefix,hroot,LocalEmbedding.comp_assoc,
    LocalEmbedding.global_ofPrefix,twist_prefix_inv,← LocalEmbedding.comp_assoc,
    GermBrick.mk_gauge,LocalEmbedding.comp_assoc]
  change GermBrick.groupEquiv ρ g
    (GermBrick.mk ρ (expandedChart ρ B F.pattern ⟨b,k⟩)) ∈ _
  rw [F.chart_eq]
  exact Finset.mem_map.mpr ⟨_,(F.leaves ⟨b,k⟩).property,rfl⟩

end TwistedBrin.Basis

namespace TwistedBrin.Prefix
variable {S : Type u}

noncomputable def splitEquiv (s : S) : Bool × Box S ≃ Box S where
  toFun z := (cut s z.1).chart z.2
  invFun x := ⟨(x s).get 0,(cut s ((x s).get 0)).tail x⟩
  left_inv := by
    rintro ⟨b,x⟩
    have hb : (((cut s b).chart x) s).get 0 = b :=
      (mem_cut_iff s b _).mp (chart_mem_brick _ _)
    simp only [hb,tail_chart]
  right_inv x := chart_tail ((mem_cut_iff s ((x s).get 0) x).mpr rfl)

@[simp] lemma splitEquiv_apply (s : S) (b : Bool) (x : Box S) :
    splitEquiv s (b,x) = (cut s b).chart x := rfl

end TwistedBrin.Prefix

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace LocalEmbedding

noncomputable def glueTwo (s : S) (h : Bool → LocalEmbedding ρ)
    (hd : Disjoint (Set.range (h false)) (Set.range (h true))) : LocalEmbedding ρ := by
  let f : Bool × Box S → Box S := fun z => h z.1 z.2
  have hf : Function.Injective f := by
    rintro ⟨b,x⟩ ⟨c,y⟩ he
    cases b <;> cases c
    · congr 1
      exact (h false).toEmbedding.injective he
    · exact False.elim ((Set.disjoint_left.mp hd) ⟨x,rfl⟩ ⟨y,he.symm⟩)
    · exact False.elim ((Set.disjoint_left.mp hd) ⟨y,he.symm⟩ ⟨x,rfl⟩)
    · congr 1
      exact (h true).toEmbedding.injective he
  let g : Box S → Box S := f ∘ (Prefix.splitEquiv s).symm
  have hg (b : Bool) (x : Box S) : g ((Prefix.cut s b).chart x) = h b x := by
    change f ((Prefix.splitEquiv s).symm (Prefix.splitEquiv s (b,x))) = _
    rw [Equiv.symm_apply_apply]
  exact {
    toEmbedding := ⟨g,hf.comp (Prefix.splitEquiv s).symm.injective⟩
    locally_standard := locallyStandard_of_charts ρ
      (fun b : Bool => ofPrefix ρ (Prefix.cut s b)) h
      (fun x => by
        obtain ⟨⟨b,y⟩,hy⟩ := (Prefix.splitEquiv s).surjective x
        exact ⟨b,y,hy⟩) g hg }

@[simp] lemma glueTwo_chart (s : S) (h : Bool → LocalEmbedding ρ)
    (hd : Disjoint (Set.range (h false)) (Set.range (h true))) (b : Bool) (x : Box S) :
    glueTwo ρ s h hd ((Prefix.cut s b).chart x) = h b x := by
  change h ((Prefix.splitEquiv s).symm (Prefix.splitEquiv s (b,x))).1
    ((Prefix.splitEquiv s).symm (Prefix.splitEquiv s (b,x))).2 = _
  rw [Equiv.symm_apply_apply]

lemma glueTwo_comp (s : S) (h : Bool → LocalEmbedding ρ)
    (hd : Disjoint (Set.range (h false)) (Set.range (h true))) (b : Bool) :
    comp ρ (glueTwo ρ s h hd) (ofPrefix ρ (Prefix.cut s b)) = h b := by
  apply LocalEmbedding.ext
  exact glueTwo_chart ρ s h hd b

lemma range_glueTwo (s : S) (h : Bool → LocalEmbedding ρ)
    (hd : Disjoint (Set.range (h false)) (Set.range (h true))) :
    Set.range (glueTwo ρ s h hd) = Set.range (h false) ∪ Set.range (h true) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    obtain ⟨⟨b,z⟩,rfl⟩ := (Prefix.splitEquiv s).surjective y
    rw [Prefix.splitEquiv_apply,glueTwo_chart]
    cases b
    · exact Or.inl ⟨z,rfl⟩
    · exact Or.inr ⟨z,rfl⟩
  · rintro (⟨y,rfl⟩ | ⟨y,rfl⟩)
    · exact ⟨(Prefix.cut s false).chart y,glueTwo_chart ρ s h hd false y⟩
    · exact ⟨(Prefix.cut s true).chart y,glueTwo_chart ρ s h hd true y⟩

end LocalEmbedding
namespace Basis

noncomputable def chartPartitionEquiv {I : Type*} [Fintype I]
    (h : I → LocalEmbedding ρ) (hp : ∀ x : Box S, ∃! i, x ∈ Set.range (h i)) :
    I ≃ ofChartPartition ρ h hp := by
  classical
  let f : I → ofChartPartition ρ h hp := fun i =>
    ⟨GermBrick.mk ρ (h i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j he
    exact chartPartition_injective ρ h hp (congrArg Subtype.val he)
  · intro b
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp b.property
    exact ⟨i,Subtype.ext hi⟩

@[simp] lemma chartPartitionEquiv_val {I : Type*} [Fintype I]
    (h : I → LocalEmbedding ρ) (hp : ∀ x : Box S, ∃! i, x ∈ Set.range (h i)) (i : I) :
    (chartPartitionEquiv ρ h hp i).val = GermBrick.mk ρ (h i) := rfl

lemma cutRefines_ofChartPartition {I : Type*} [Fintype I]
    (h : I → LocalEmbedding ρ) (hp : ∀ x : Box S, ∃! i, x ∈ Set.range (h i))
    (C : Basis ρ) (P : I → Pattern S)
    (hm : ∀ i j, GermBrick.mk ρ (LocalEmbedding.comp ρ (h i)
      (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (P i) j))) ∈ C.pieces) :
    CutRefines ρ (ofChartPartition ρ h hp) C := by
  classical
  let B := ofChartPartition ρ h hp
  let e := chartPartitionEquiv ρ h hp
  have hg (i : I) : ∃ a : A, chart ρ B (e i) =
      LocalEmbedding.comp ρ (h i) (LocalEmbedding.global ρ a) := by
    apply (GermBrick.mk_eq_iff ρ _ _).mp
    exact GermBrick.mk_representative ρ _
  choose a ha using hg
  let Q := fun b : B => Pattern.relabel (ρ (a (e.symm b))⁻¹) (P (e.symm b))
  apply Nonempty.intro
  apply Forest.of_mem ρ Q
  rintro ⟨b,j⟩
  let i := e.symm b
  have hroot : chart ρ B b = LocalEmbedding.comp ρ (h i) (LocalEmbedding.global ρ (a i)) := by
    have hh := ha i
    change chart ρ B (e (e.symm b)) = _ at hh
    rwa [e.apply_symm_apply] at hh
  obtain ⟨k,rfl⟩ := (Pattern.relabelLeaves (ρ (a i)⁻¹) (P i)).surjective j
  change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B b)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (Pattern.relabel (ρ (a i)⁻¹) (P i))
      (Pattern.relabelLeaves (ρ (a i)⁻¹) (P i) k)))) ∈ _
  rw [Pattern.relabel_prefix,hroot,LocalEmbedding.comp_assoc,LocalEmbedding.global_ofPrefix,
    twist_prefix_inv,← LocalEmbedding.comp_assoc,GermBrick.mk_gauge]
  exact hm i k

end Basis
end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

lemma chart_germ (C : Basis ρ) (c : C) : GermBrick.mk ρ (chart ρ C c) = c.val :=
  GermBrick.mk_representative ρ _

lemma regions_disjoint (C : Basis ρ) {a b : C} (hab : a ≠ b) :
    Disjoint (GermBrick.region ρ a.val) (GermBrick.region ρ b.val) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hab ((C.partition x).unique hx hy)

structure Merge (C : Basis ρ) where
  first : C
  second : C
  distinct : first ≠ second
  coordinate : S
  joined : LocalEmbedding ρ
  left_eq : GermBrick.mk ρ (LocalEmbedding.comp ρ joined
    (LocalEmbedding.ofPrefix ρ (Prefix.cut coordinate false))) = first.val
  right_eq : GermBrick.mk ρ (LocalEmbedding.comp ρ joined
    (LocalEmbedding.ofPrefix ρ (Prefix.cut coordinate true))) = second.val

namespace Merge
variable {ρ} {C : Basis ρ}

noncomputable def ofPair (a b : C) (hab : a ≠ b) (s : S) : Merge ρ C := by
  let h : Bool → LocalEmbedding ρ := fun q => if q then chart ρ C b else chart ρ C a
  have hd : Disjoint (Set.range (h false)) (Set.range (h true)) := by
    dsimp [h]
    rw [chart_region,chart_region]
    exact regions_disjoint ρ C hab
  exact {
    first := a
    second := b
    distinct := hab
    coordinate := s
    joined := LocalEmbedding.glueTwo ρ s h hd
    left_eq := by rw [LocalEmbedding.glueTwo_comp]; exact chart_germ ρ C a
    right_eq := by rw [LocalEmbedding.glueTwo_comp]; exact chart_germ ρ C b }

lemma range_joined (m : Merge ρ C) : Set.range m.joined =
    GermBrick.region ρ m.first.val ∪ GermBrick.region ρ m.second.val := by
  have h (q : Bool) : Set.range (fun x => m.joined ((Prefix.cut m.coordinate q).chart x)) =
      GermBrick.region ρ (if q then m.second.val else m.first.val) := by
    cases q
    · change GermBrick.region ρ (GermBrick.mk ρ (LocalEmbedding.comp ρ m.joined
        (LocalEmbedding.ofPrefix ρ (Prefix.cut m.coordinate false)))) = _
      simp only [m.left_eq,Bool.false_eq_true,ite_false]
    · change GermBrick.region ρ (GermBrick.mk ρ (LocalEmbedding.comp ρ m.joined
        (LocalEmbedding.ofPrefix ρ (Prefix.cut m.coordinate true)))) = _
      simp only [m.right_eq,ite_true]
  have h0 := h false
  have h1 := h true
  simp only [Bool.false_eq_true,ite_false,ite_true] at h0 h1
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    obtain ⟨⟨q,z⟩,rfl⟩ := (Prefix.splitEquiv m.coordinate).surjective y
    have hz : m.joined ((Prefix.cut m.coordinate q).chart z) ∈
        GermBrick.region ρ (if q then m.second.val else m.first.val) := by
      rw [← h q]; exact ⟨z,rfl⟩
    cases q
    · exact Or.inl hz
    · exact Or.inr hz
  · intro hx
    rcases hx with hx | hx
    · rw [← h0] at hx
      obtain ⟨y,rfl⟩ := hx
      exact ⟨_,rfl⟩
    · rw [← h1] at hx
      obtain ⟨y,rfl⟩ := hx
      exact ⟨_,rfl⟩

abbrev Rest (m : Merge ρ C) := {c : C // c ≠ m.first ∧ c ≠ m.second}
abbrev Roots (m : Merge ρ C) := Option m.Rest

noncomputable def leafEquiv (m : Merge ρ C) : Bool ⊕ m.Rest ≃ C := by
  classical
  let f : Bool ⊕ m.Rest → C := Sum.elim (fun q => if q then m.second else m.first) Subtype.val
  apply Equiv.ofBijective f
  constructor
  · intro i j he
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        cases i <;> cases j <;> simp_all [f,m.distinct,Ne.symm m.distinct]
      | inr j =>
        cases i
        · exact False.elim (j.property.1 he.symm)
        · exact False.elim (j.property.2 he.symm)
    | inr i =>
      cases j with
      | inl j =>
        cases j
        · exact False.elim (i.property.1 he)
        · exact False.elim (i.property.2 he)
      | inr j => exact congrArg Sum.inr (Subtype.ext he)
  · intro c
    by_cases hc : c = m.first
    · exact ⟨Sum.inl false,hc.symm⟩
    by_cases hd : c = m.second
    · exact ⟨Sum.inl true,hd.symm⟩
    exact ⟨Sum.inr ⟨c,hc,hd⟩,rfl⟩

noncomputable def rootChart (m : Merge ρ C) : m.Roots → LocalEmbedding ρ
  | none => m.joined
  | some c => chart ρ C c.val

lemma rootPartition (m : Merge ρ C) :
    ∀ x : Box S, ∃! r : m.Roots, x ∈ Set.range (m.rootChart r) := by
  classical
  intro x
  obtain ⟨c,hc,hu⟩ := C.partition x
  have hnone : x ∈ Set.range (m.rootChart none) ↔ c = m.first ∨ c = m.second := by
    change x ∈ Set.range m.joined ↔ _
    rw [m.range_joined]
    constructor
    · rintro (hx | hx)
      · exact Or.inl ((hu _ hx).symm)
      · exact Or.inr ((hu _ hx).symm)
    · rintro (rfl | rfl)
      · exact Or.inl hc
      · exact Or.inr hc
  have hsome (r : m.Rest) : x ∈ Set.range (m.rootChart (some r)) ↔ r.val = c := by
    change x ∈ Set.range (chart ρ C r.val) ↔ _
    rw [chart_region]
    exact ⟨hu _,fun he => by rw [he]; exact hc⟩
  by_cases h : c = m.first ∨ c = m.second
  · refine ⟨none,hnone.mpr h,?_⟩
    intro r hr
    cases r with
    | none => rfl
    | some r =>
      have he := (hsome r).mp hr
      rcases h with h | h
      · exact False.elim (r.property.1 (he.trans h))
      · exact False.elim (r.property.2 (he.trans h))
  · have hh : c ≠ m.first ∧ c ≠ m.second := not_or.mp h
    refine ⟨some ⟨c,hh⟩,(hsome _).mpr rfl,?_⟩
    intro r hr
    cases r with
    | none => exact False.elim (h (hnone.mp hr))
    | some r => exact congrArg some (Subtype.ext ((hsome r).mp hr))

noncomputable def lower (m : Merge ρ C) : Basis ρ := by
  classical
  exact ofChartPartition ρ m.rootChart m.rootPartition

lemma rank_lower (m : Merge ρ C) : rank ρ m.lower + 1 = rank ρ C := by
  classical
  rw [lower,rank_ofChartPartition,rank_eq_card]
  have hc := Fintype.card_congr m.leafEquiv
  simp only [Fintype.card_sum,Fintype.card_bool] at hc
  change Fintype.card (Option m.Rest) + 1 = Fintype.card C
  rw [Fintype.card_option]
  omega

lemma lower_cutRefines (m : Merge ρ C) : CutRefines ρ m.lower C := by
  classical
  let P : m.Roots → Pattern S := fun r => match r with
    | none => .split m.coordinate .leaf .leaf
    | some _ => .leaf
  apply cutRefines_ofChartPartition ρ m.rootChart m.rootPartition C P
  intro r j
  cases r with
  | none =>
    cases j with
    | inl j =>
      simp [P,Pattern.leafPrefix,Prefix.append_empty,rootChart,m.left_eq]
    | inr j =>
      simp [P,Pattern.leafPrefix,Prefix.append_empty,rootChart,m.right_eq]
  | some r =>
    simp [P,Pattern.leafPrefix,rootChart,LocalEmbedding.ofPrefix_empty,
      LocalEmbedding.comp_identity,chart_germ]

lemma lower_ne (m : Merge ρ C) : m.lower ≠ C := by
  intro he
  have hr := m.rank_lower
  rw [he] at hr
  omega

end Merge
end Basis
end TwistedBrin

namespace TwistedBrin.Pattern
variable {S : Type u}

@[simp] lemma graft_leaf (P : Pattern S) : graft P (fun _ => leaf) = P := by
  induction P with
  | leaf => rfl
  | split s P Q ihP ihQ => simp only [graft,ihP,ihQ]

noncomputable def insert (P : Pattern S) (i : Leaves P) (s : S) : Pattern S := by
  classical
  exact graft P (fun j => if j = i then split s leaf leaf else leaf)

lemma insert_leaf (s : S) : insert leaf () s = split s leaf leaf := by
  classical
  simp [insert,graft,Leaves]

lemma insert_left (P Q : Pattern S) (i : Leaves P) (s t : S) :
    insert (split s P Q) (Sum.inl i) t = split s (insert P i t) Q := by
  classical
  simp only [insert,graft,Leaves,Sum.inl.injEq,Sum.inr_ne_inl,ite_false,graft_leaf]

lemma insert_right (P Q : Pattern S) (i : Leaves Q) (s t : S) :
    insert (split s P Q) (Sum.inr i) t = split s P (insert Q i t) := by
  classical
  simp only [insert,graft,Leaves,Sum.inr.injEq,Sum.inl_ne_inr,ite_false,graft_leaf]

lemma exists_prune (P : Pattern S) (hP : P ≠ leaf) :
    ∃ Q : Pattern S, ∃ i : Leaves Q, ∃ s : S, insert Q i s = P := by
  classical
  induction P with
  | leaf => exact False.elim (hP rfl)
  | split s P Q ihP ihQ =>
    by_cases hp : P = leaf
    · subst P
      by_cases hq : Q = leaf
      · subst Q
        exact ⟨leaf,(),s,insert_leaf s⟩
      · obtain ⟨R,i,t,hi⟩ := ihQ hq
        exact ⟨split s leaf R,Sum.inr i,t,by rw [insert_right,hi]⟩
    · obtain ⟨R,i,t,hi⟩ := ihP hp
      exact ⟨split s R Q,Sum.inl i,t,by rw [insert_left,hi]⟩

end TwistedBrin.Pattern

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
namespace Basis.Merge
variable {C : Basis ρ}

lemma germ_mem_lower_iff (m : Merge ρ C) (g : GermBrick ρ) :
    g ∈ m.lower.pieces ↔ g = GermBrick.mk ρ m.joined ∨
      (g ∈ C.pieces ∧ g ≠ m.first.val ∧ g ≠ m.second.val) := by
  classical
  change g ∈ Finset.univ.image (fun r : m.Roots => GermBrick.mk ρ (m.rootChart r)) ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨r,_,hr⟩
    cases r with
    | none => exact Or.inl hr.symm
    | some c =>
      have he : c.val.val = g := (chart_germ ρ C c.val).symm.trans hr
      refine Or.inr ⟨he ▸ c.val.property,?_,?_⟩
      · intro h; exact c.property.1 (Subtype.ext (he.trans h))
      · intro h; exact c.property.2 (Subtype.ext (he.trans h))
  · rintro (hg | ⟨hg,hf,hs⟩)
    · exact ⟨none,Finset.mem_univ _,hg.symm⟩
    · let c : C := ⟨g,hg⟩
      have hc : c ≠ m.first ∧ c ≠ m.second :=
        ⟨fun h => hf (congrArg Subtype.val h),fun h => hs (congrArg Subtype.val h)⟩
      exact ⟨some ⟨c,hc⟩,Finset.mem_univ _,chart_germ ρ C c⟩

lemma joined_ne_piece (m : Merge ρ C) (c : C) : GermBrick.mk ρ m.joined ≠ c.val := by
  intro he
  have hr : Set.range m.joined = GermBrick.region ρ c.val := congrArg (GermBrick.region ρ) he
  have ha : m.first = c := by
    obtain ⟨x,hx⟩ := GermBrick.region_nonempty ρ m.first.val
    exact (C.partition x).unique hx (hr ▸ m.range_joined.symm ▸ Or.inl hx)
  have hb : m.second = c := by
    obtain ⟨x,hx⟩ := GermBrick.region_nonempty ρ m.second.val
    exact (C.partition x).unique hx (hr ▸ m.range_joined.symm ▸ Or.inr hx)
  exact m.distinct (ha.trans hb.symm)

noncomputable def toLower (m : Merge ρ C) (c : C) (hc : c ≠ m.first ∧ c ≠ m.second) : m.lower :=
  ⟨c.val,(m.germ_mem_lower_iff c.val).mpr (Or.inr ⟨c.property,
    fun h => hc.1 (Subtype.ext h),fun h => hc.2 (Subtype.ext h)⟩)⟩

@[simp] lemma toLower_val (m : Merge ρ C) (c : C) (hc) : (m.toLower c hc).val = c.val := rfl

def Disjoint (m n : Merge ρ C) : Prop :=
  m.first ≠ n.first ∧ m.first ≠ n.second ∧ m.second ≠ n.first ∧ m.second ≠ n.second

lemma disjoint_symm {m n : Merge ρ C} (h : m.Disjoint n) : n.Disjoint m :=
  ⟨Ne.symm h.1,Ne.symm h.2.2.1,Ne.symm h.2.1,Ne.symm h.2.2.2⟩

noncomputable def lift {m n : Merge ρ C} (h : m.Disjoint n) : Merge ρ m.lower where
  first := m.toLower n.first ⟨Ne.symm h.1,Ne.symm h.2.2.1⟩
  second := m.toLower n.second ⟨Ne.symm h.2.1,Ne.symm h.2.2.2⟩
  distinct := by
    intro he
    apply n.distinct
    apply Subtype.ext
    exact congrArg (fun c : m.lower => c.val) he
  coordinate := n.coordinate
  joined := n.joined
  left_eq := n.left_eq
  right_eq := n.right_eq

lemma lower_lift_comm {m n : Merge ρ C} (h : m.Disjoint n) :
    (lift h).lower = (lift (disjoint_symm h)).lower := by
  classical
  apply Basis.ext
  ext g
  simp only [germ_mem_lower_iff]
  change (g = GermBrick.mk ρ n.joined ∨
      ((g = GermBrick.mk ρ m.joined ∨
        (g ∈ C.pieces ∧ g ≠ m.first.val ∧ g ≠ m.second.val)) ∧
        g ≠ n.first.val ∧ g ≠ n.second.val)) ↔
    (g = GermBrick.mk ρ m.joined ∨
      ((g = GermBrick.mk ρ n.joined ∨
        (g ∈ C.pieces ∧ g ≠ n.first.val ∧ g ≠ n.second.val)) ∧
        g ≠ m.first.val ∧ g ≠ m.second.val))
  have hm1 := m.joined_ne_piece n.first
  have hm2 := m.joined_ne_piece n.second
  have hn1 := n.joined_ne_piece m.first
  have hn2 := n.joined_ne_piece m.second
  aesop

lemma common_lower_of_disjoint {m n : Merge ρ C} (h : m.Disjoint n) :
    ∃ D : Basis ρ, CutRefines ρ D m.lower ∧ CutRefines ρ D n.lower := by
  refine ⟨(lift h).lower,(lift h).lower_cutRefines,?_⟩
  rw [lower_lift_comm h]
  exact (lift (disjoint_symm h)).lower_cutRefines

end Basis.Merge
end TwistedBrin

end

end OAI
