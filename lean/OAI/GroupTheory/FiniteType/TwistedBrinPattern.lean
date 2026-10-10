import Mathlib
import OAI.GroupTheory.FiniteType.TwistedBrinBasisTranslateEquiv

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
namespace TwistedBrin.Pattern
variable {S : Type u}

structure Pruning (P : Pattern S) where
  shorter : Pattern S
  stem : Prefix S
  coordinate : S
  first : Leaves P
  second : Leaves P
  distinct : first ≠ second
  first_prefix : leafPrefix P first = stem.append (Prefix.cut coordinate false)
  second_prefix : leafPrefix P second = stem.append (Prefix.cut coordinate true)
  remaining : ∀ i : Leaves shorter, leafPrefix shorter i = stem ∨
    ∃ j : Leaves P, leafPrefix shorter i = leafPrefix P j ∧ j ≠ first ∧ j ≠ second

lemma pruning_exists (P : Pattern S) (hP : P ≠ leaf) : Nonempty (Pruning P) := by
  induction P with
  | leaf => exact False.elim (hP rfl)
  | split s P Q ihP ihQ =>
    by_cases hp : P = leaf
    · subst P
      by_cases hq : Q = leaf
      · subst Q
        exact ⟨{
          shorter := leaf
          stem := Prefix.empty
          coordinate := s
          first := Sum.inl ()
          second := Sum.inr ()
          distinct := Sum.inl_ne_inr
          first_prefix := by simp [leafPrefix]
          second_prefix := by simp [leafPrefix]
          remaining := fun _ => Or.inl rfl }⟩
      · obtain ⟨T⟩ := ihQ hq
        refine ⟨{
          shorter := split s leaf T.shorter
          stem := (Prefix.cut s true).append T.stem
          coordinate := T.coordinate
          first := Sum.inr T.first
          second := Sum.inr T.second
          distinct := fun he => T.distinct (Sum.inr.inj he)
          first_prefix := ?_
          second_prefix := ?_
          remaining := ?_ }⟩
        · change (Prefix.cut s true).append (leafPrefix Q T.first) = _
          rw [T.first_prefix,Prefix.append_assoc]
        · change (Prefix.cut s true).append (leafPrefix Q T.second) = _
          rw [T.second_prefix,Prefix.append_assoc]
        · intro i
          cases i with
          | inl i =>
            exact Or.inr ⟨Sum.inl i,rfl,Sum.inl_ne_inr,Sum.inl_ne_inr⟩
          | inr i =>
            rcases T.remaining i with he | ⟨j,hj,hf,hs⟩
            · exact Or.inl (congrArg (Prefix.append (Prefix.cut s true)) he)
            · exact Or.inr ⟨Sum.inr j,congrArg (Prefix.append (Prefix.cut s true)) hj,
                fun h => hf (Sum.inr.inj h),fun h => hs (Sum.inr.inj h)⟩
    · obtain ⟨T⟩ := ihP hp
      refine ⟨{
        shorter := split s T.shorter Q
        stem := (Prefix.cut s false).append T.stem
        coordinate := T.coordinate
        first := Sum.inl T.first
        second := Sum.inl T.second
        distinct := fun he => T.distinct (Sum.inl.inj he)
        first_prefix := ?_
        second_prefix := ?_
        remaining := ?_ }⟩
      · change (Prefix.cut s false).append (leafPrefix P T.first) = _
        rw [T.first_prefix,Prefix.append_assoc]
      · change (Prefix.cut s false).append (leafPrefix P T.second) = _
        rw [T.second_prefix,Prefix.append_assoc]
      · intro i
        cases i with
        | inl i =>
          rcases T.remaining i with he | ⟨j,hj,hf,hs⟩
          · exact Or.inl (congrArg (Prefix.append (Prefix.cut s false)) he)
          · exact Or.inr ⟨Sum.inl j,congrArg (Prefix.append (Prefix.cut s false)) hj,
              fun h => hf (Sum.inl.inj h),fun h => hs (Sum.inl.inj h)⟩
        | inr i =>
          exact Or.inr ⟨Sum.inr i,rfl,Sum.inr_ne_inl,Sum.inr_ne_inl⟩

end TwistedBrin.Pattern

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
namespace Basis.Forest
variable {B C : Basis ρ}

lemma eq_of_all_leaf (F : Forest ρ B C) (h : ∀ b, F.pattern b = .leaf) : B = C := by
  apply eq_of_le_of_rank_eq ρ F.refines
  rw [rank_eq_card,rank_eq_card]
  have hc := Fintype.card_congr F.leaves
  rw [Fintype.card_sigma] at hc
  have hf (b : B) : Fintype.card (Pattern.Leaves (F.pattern b)) = 1 := by
    rw [h b]
    change Fintype.card Unit = 1
    exact Fintype.card_unique
  simp_rw [hf] at hc
  simpa using hc

noncomputable def prunedMerge (F : Forest ρ B C) (b : B) (T : Pattern.Pruning (F.pattern b)) :
    Merge ρ C where
  first := F.leaves ⟨b,T.first⟩
  second := F.leaves ⟨b,T.second⟩
  distinct := by
    intro he
    have hh := F.leaves.injective he
    exact T.distinct (by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hh)
  coordinate := T.coordinate
  joined := LocalEmbedding.comp ρ (chart ρ B b) (LocalEmbedding.ofPrefix ρ T.stem)
  left_eq := by
    rw [LocalEmbedding.comp_assoc,← LocalEmbedding.ofPrefix_append,← T.first_prefix]
    exact F.chart_eq ⟨b,T.first⟩
  right_eq := by
    rw [LocalEmbedding.comp_assoc,← LocalEmbedding.ofPrefix_append,← T.second_prefix]
    exact F.chart_eq ⟨b,T.second⟩

lemma cutRefines_pruned (F : Forest ρ B C) (b : B) (T : Pattern.Pruning (F.pattern b)) :
    CutRefines ρ B (F.prunedMerge b T).lower := by
  classical
  let m := F.prunedMerge b T
  let Q := Function.update F.pattern b T.shorter
  have hmem (i : F.Index) (hf : i ≠ ⟨b,T.first⟩) (hs : i ≠ ⟨b,T.second⟩) :
      GermBrick.mk ρ (expandedChart ρ B F.pattern i) ∈ m.lower.pieces := by
    rw [F.chart_eq]
    apply (m.germ_mem_lower_iff _).mpr
    refine Or.inr ⟨(F.leaves i).property,?_,?_⟩
    · intro he
      exact hf (F.leaves.injective (Subtype.ext he))
    · intro he
      exact hs (F.leaves.injective (Subtype.ext he))
  apply Nonempty.intro
  apply Forest.of_mem ρ Q
  rintro ⟨c,j⟩
  change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B c)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (Q c) j))) ∈ m.lower.pieces
  by_cases hc : c = b
  · subst c
    have hT (R : Pattern S) (hR : R = T.shorter) (i : Pattern.Leaves R) :
        GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B b)
          (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix R i))) ∈ m.lower.pieces := by
      subst R
      rcases T.remaining i with he | ⟨k,hk,hf,hs⟩
      · rw [he]
        exact (m.germ_mem_lower_iff _).mpr (Or.inl rfl)
      · rw [hk]
        exact hmem ⟨b,k⟩ (by
          intro h; exact hf (by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h)) (by
          intro h; exact hs (by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h))
    exact hT (Q b) (Function.update_self b T.shorter F.pattern) j
  · have hT (R : Pattern S) (hR : R = F.pattern c) (i : Pattern.Leaves R) :
        GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B c)
          (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix R i))) ∈ m.lower.pieces := by
      subst R
      exact hmem ⟨c,i⟩ (fun h => hc (congrArg Sigma.fst h))
        (fun h => hc (congrArg Sigma.fst h))
    exact hT (Q c) (Function.update_of_ne hc T.shorter F.pattern) j

lemma exists_last_merge (F : Forest ρ B C) (hne : B ≠ C) :
    ∃ m : Merge ρ C, CutRefines ρ B m.lower := by
  classical
  have hn : ∃ b, F.pattern b ≠ .leaf := by
    by_contra h
    exact hne (F.eq_of_all_leaf (by simpa only [not_exists,not_not] using h))
  obtain ⟨b,hb⟩ := hn
  obtain ⟨T⟩ := Pattern.pruning_exists (F.pattern b) hb
  exact ⟨F.prunedMerge b T,F.cutRefines_pruned b T⟩

end Basis.Forest
end

section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

abbrev Descending (C : Basis ρ) := {B : Basis ρ // CutRefines ρ B C ∧ B ≠ C}

def DownAdjacent {C : Basis ρ} (B D : Descending ρ C) : Prop :=
  CutRefines ρ B.val D.val ∨ CutRefines ρ D.val B.val

abbrev DownConnected {C : Basis ρ} (B D : Descending ρ C) : Prop :=
  Relation.ReflTransGen (DownAdjacent ρ) B D

namespace Merge
variable {ρ} {C : Basis ρ}

noncomputable def vertex (m : Merge ρ C) : Descending ρ C :=
  ⟨m.lower,m.lower_cutRefines,m.lower_ne⟩

lemma connected_of_disjoint {m n : Merge ρ C} (h : m.Disjoint n) :
    DownConnected ρ m.vertex n.vertex := by
  obtain ⟨D,hDm,hDn⟩ := common_lower_of_disjoint h
  have hDC := cutRefines_trans ρ hDm m.lower_cutRefines
  have hne : D ≠ C := by
    intro he
    subst D
    exact m.lower_ne (cutRefines_antisymm ρ m.lower_cutRefines hDm)
  let v : Descending ρ C := ⟨D,hDC,hne⟩
  exact (Relation.ReflTransGen.single (b := v) (Or.inr hDm)).trans
    (Relation.ReflTransGen.single (Or.inl hDn))

lemma exists_disjoint_pair [Nonempty S] (m n : Merge ρ C) (hc : 6 ≤ rank ρ C) :
    ∃ r : Merge ρ C, m.Disjoint r ∧ r.Disjoint n := by
  classical
  let U : Finset C := {m.first,m.second} ∪ {n.first,n.second}
  have hU : U.card ≤ 4 := by
    have hm : ({m.first,m.second} : Finset C).card = 2 := Finset.card_pair m.distinct
    have hn : ({n.first,n.second} : Finset C).card = 2 := Finset.card_pair n.distinct
    have h := Finset.card_union_le ({m.first,m.second} : Finset C) {n.first,n.second}
    dsimp [U]
    omega
  have hv : 1 < (Finset.univ \ U).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U),Finset.card_univ]
    rw [rank_eq_card] at hc
    omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hv
  have haq : a ≠ m.first ∧ a ≠ m.second ∧ a ≠ n.first ∧ a ≠ n.second := by
    simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,U,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,not_or,and_assoc] using ha
  have hbq : b ≠ m.first ∧ b ≠ m.second ∧ b ≠ n.first ∧ b ≠ n.second := by
    simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,U,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,not_or,and_assoc] using hb
  let r := ofPair a b hab (Classical.choice (inferInstance : Nonempty S))
  refine ⟨r,?_,?_⟩
  · exact ⟨Ne.symm haq.1,Ne.symm hbq.1,Ne.symm haq.2.1,Ne.symm hbq.2.1⟩
  · exact ⟨haq.2.2.1,haq.2.2.2,hbq.2.2.1,hbq.2.2.2⟩

lemma connected [Nonempty S] (m n : Merge ρ C) (hc : 6 ≤ rank ρ C) :
    DownConnected ρ m.vertex n.vertex := by
  obtain ⟨r,hm,hn⟩ := exists_disjoint_pair m n hc
  exact (connected_of_disjoint hm).trans (connected_of_disjoint hn)

end Merge

lemma descending_connected [Nonempty S] (C : Basis ρ) (hc : 6 ≤ rank ρ C)
    (B D : Descending ρ C) : DownConnected ρ B D := by
  obtain ⟨m,hm⟩ := B.property.1.some.exists_last_merge B.property.2
  obtain ⟨n,hn⟩ := D.property.1.some.exists_last_merge D.property.2
  exact (Relation.ReflTransGen.single (b := m.vertex) (Or.inl hm)).trans
    ((m.connected n hc).trans (Relation.ReflTransGen.single (Or.inr hn)))

end Basis
end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma Oligomorphic.finite_palette (h : Oligomorphic ρ) (n : ℕ) :
    ∃ U : Finset S, ∀ F : Finset S, F.card ≤ n →
      ∃ a : A, F.map (ρ a).toEmbedding ⊆ U := by
  classical
  choose R hR using h
  let U := (Finset.range (n+1)).biUnion (fun k => (R k).biUnion id)
  refine ⟨U,fun F hF => ?_⟩
  obtain ⟨E,hE,a,ha⟩ := hR F.card F rfl
  refine ⟨a,?_⟩
  rw [ha]
  intro s hs
  exact Finset.mem_biUnion.mpr ⟨F.card,Finset.mem_range.mpr (by omega),
    Finset.mem_biUnion.mpr ⟨E,hE,hs⟩⟩

end TwistedBrin

namespace TwistedBrin.Pattern
variable {S : Type u}

def nodes : Pattern S → ℕ
  | .leaf => 0
  | .split _ P Q => nodes P + nodes Q + 1

def depth : Pattern S → ℕ
  | .leaf => 0
  | .split _ P Q => max (depth P) (depth Q) + 1

noncomputable def coordinates : Pattern S → Finset S
  | .leaf => ∅
  | .split s P Q => by classical exact Insert.insert s (coordinates P ∪ coordinates Q)

lemma nodes_add_one (P : Pattern S) : nodes P + 1 = Fintype.card (Leaves P) := by
  induction P with
  | leaf => change 0 + 1 = Fintype.card Unit; simp
  | split s P Q ihP ihQ =>
    change nodes P + nodes Q + 1 + 1 = Fintype.card (Leaves P ⊕ Leaves Q)
    rw [Fintype.card_sum,← ihP,← ihQ]
    omega

lemma depth_le_nodes (P : Pattern S) : depth P ≤ nodes P := by
  induction P with
  | leaf => rfl
  | split s P Q ihP ihQ => simp only [depth,nodes]; omega

lemma coordinates_card_le (P : Pattern S) : (coordinates P).card ≤ nodes P := by
  classical
  induction P with
  | leaf => simp [coordinates,nodes]
  | split s P Q ihP ihQ =>
    have h₁ := Finset.card_insert_le s (coordinates P ∪ coordinates Q)
    have h₂ := Finset.card_union_le (coordinates P) (coordinates Q)
    simp only [coordinates,nodes]
    omega

lemma coordinates_relabel (σ : Equiv.Perm S) (P : Pattern S) :
    coordinates (relabel σ P) = (coordinates P).map σ.toEmbedding := by
  classical
  induction P with
  | leaf => simp [relabel,coordinates]
  | split s P Q ihP ihQ => simp [relabel,coordinates,ihP,ihQ,Finset.map_union]

@[simp] lemma depth_relabel (σ : Equiv.Perm S) (P : Pattern S) :
    depth (relabel σ P) = depth P := by
  induction P with
  | leaf => rfl
  | split s P Q ihP ihQ => simp [relabel,depth,ihP,ihQ]

noncomputable def bounded (U : Finset S) : ℕ → Finset (Pattern S)
  | 0 => {.leaf}
  | n+1 => by
    classical
    exact Insert.insert .leaf (U.biUnion (fun s => (bounded U n).biUnion (fun P =>
      (bounded U n).image (fun Q => .split s P Q))))

lemma mem_bounded (U : Finset S) (n : ℕ) (P : Pattern S)
    (hP : coordinates P ⊆ U) (hd : depth P ≤ n) : P ∈ bounded U n := by
  classical
  induction n generalizing P with
  | zero =>
    cases P with
    | leaf => simp [bounded]
    | split s P Q => simp only [depth] at hd; omega
  | succ n ih =>
    cases P with
    | leaf => simp [bounded]
    | split s P Q =>
      have hs : s ∈ U := hP (by simp [coordinates])
      have hP' : coordinates P ⊆ U := fun x hx => hP (by simp [coordinates,hx])
      have hQ' : coordinates Q ⊆ U := fun x hx => hP (by simp [coordinates,hx])
      have hdP : depth P ≤ n := by simp only [depth] at hd; omega
      have hdQ : depth Q ≤ n := by simp only [depth] at hd; omega
      simp only [bounded,Finset.mem_insert,Finset.mem_biUnion,Finset.mem_image]
      exact Or.inr ⟨s,hs,P,ih P hP' hdP,Q,ih Q hQ' hdQ,rfl⟩

lemma finite_orbit_representatives {A : Type v} [Group A] (ρ : A →* Equiv.Perm S)
    (h : Oligomorphic ρ) (n : ℕ) :
    ∃ R : Finset (Pattern S), ∀ P : Pattern S, Fintype.card (Leaves P) ≤ n →
      ∃ a : A, relabel (ρ a) P ∈ R := by
  classical
  obtain ⟨U,hU⟩ := h.finite_palette ρ n
  refine ⟨bounded U n,fun P hP => ?_⟩
  have hn : nodes P ≤ n := by have := nodes_add_one P; omega
  obtain ⟨a,ha⟩ := hU (coordinates P) ((coordinates_card_le P).trans hn)
  refine ⟨a,mem_bounded U n _ ?_ ?_⟩
  · rwa [coordinates_relabel]
  · rw [depth_relabel]
    exact (depth_le_nodes P).trans hn

end TwistedBrin.Pattern

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma twistPieces_expanded_germ (B : Basis ρ) (P : B → Pattern S) (a : B → A)
    (i : Σ b : B, Pattern.Leaves (P b)) :
    GermBrick.groupEquiv ρ (twistPiecesHom ρ B a)
      (GermBrick.mk ρ (expandedChart ρ B P i)) =
    GermBrick.mk ρ (expandedChart ρ B (fun b => Pattern.relabel (ρ (a b)) (P b))
      ⟨i.1,Pattern.relabelLeaves (ρ (a i.1)) (P i.1) i.2⟩) := by
  apply (GermBrick.mk_eq_iff ρ _ _).mpr
  refine ⟨a i.1,?_⟩
  apply LocalEmbedding.ext
  intro x
  change twistPieces ρ B a (chart ρ B i.1 ((Pattern.leafPrefix (P i.1) i.2).chart x)) =
    chart ρ B i.1 ((Pattern.leafPrefix (Pattern.relabel (ρ (a i.1)) (P i.1))
      (Pattern.relabelLeaves (ρ (a i.1)) (P i.1) i.2)).chart (twist ρ (a i.1) x))
  rw [twistPieces_chart,Pattern.relabel_prefix,twist_chart]

lemma translate_twistPieces_expand (B : Basis ρ) (P : B → Pattern S) (a : B → A) :
    translate ρ (twistPiecesHom ρ B a) (expand ρ B P) =
      expand ρ B (fun b => Pattern.relabel (ρ (a b)) (P b)) := by
  classical
  apply Basis.ext
  ext c
  change (c ∈ (Finset.univ.image (fun i => GermBrick.mk ρ (expandedChart ρ B P i))).map _) ↔
    c ∈ Finset.univ.image _
  simp only [Finset.mem_map,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨d,⟨i,rfl⟩,rfl⟩
    exact ⟨⟨i.1,Pattern.relabelLeaves (ρ (a i.1)) (P i.1) i.2⟩,
      (twistPieces_expanded_germ ρ B P a i).symm⟩
  · rintro ⟨⟨b,j⟩,rfl⟩
    obtain ⟨k,rfl⟩ := (Pattern.relabelLeaves (ρ (a b)) (P b)).surjective j
    exact ⟨_,⟨⟨b,k⟩,rfl⟩,twistPieces_expanded_germ ρ B P a ⟨b,k⟩⟩

lemma Forest.expand_eq {B C : Basis ρ} (F : Forest ρ B C) : expand ρ B F.pattern = C := by
  classical
  apply Basis.ext
  ext c
  change c ∈ Finset.univ.image _ ↔ c ∈ C.pieces
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    rw [F.chart_eq]
    exact (F.leaves i).property
  · intro hc
    obtain ⟨i,hi⟩ := F.leaves.surjective ⟨c,hc⟩
    exact ⟨i,(F.chart_eq i).trans (congrArg Subtype.val hi)⟩

lemma Forest.leaves_le_rank {B C : Basis ρ} (F : Forest ρ B C) (b : B) :
    Fintype.card (Pattern.Leaves (F.pattern b)) ≤ rank ρ C := by
  have hr : rank ρ C = ∑ b : B, Fintype.card (Pattern.Leaves (F.pattern b)) :=
    (congrArg (rank ρ) (F.expand_eq ρ)).symm.trans (rank_expand ρ B F.pattern)
  rw [hr]
  exact Finset.single_le_sum (f := fun b : B => Fintype.card (Pattern.Leaves (F.pattern b)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

lemma outgoing_finite_orbit_representatives (h : Oligomorphic ρ) (B : Basis ρ) (n : ℕ) :
    ∃ R : Finset (Basis ρ), ∀ C : Basis ρ, CutRefines ρ B C → rank ρ C ≤ n →
      ∃ a : B → A, translate ρ (twistPiecesHom ρ B a) C ∈ R := by
  classical
  obtain ⟨T,hT⟩ := Pattern.finite_orbit_representatives ρ h n
  let R := (Finset.univ : Finset (B → {P // P ∈ T})).image
    (fun f => expand ρ B (fun b => (f b).val))
  refine ⟨R,fun C hBC hC => ?_⟩
  obtain ⟨F⟩ := hBC
  choose a ha using fun b => hT (F.pattern b) ((F.leaves_le_rank ρ b).trans hC)
  refine ⟨a,?_⟩
  rw [← F.expand_eq ρ,translate_twistPieces_expand]
  exact Finset.mem_image.mpr ⟨fun b => ⟨_,ha b⟩,Finset.mem_univ _,rfl⟩

end TwistedBrin.Basis

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma length_le_of_brick_subset {p q : Prefix S} (h : p.brick ⊆ q.brick) (s : S) :
    (q s).length ≤ (p s).length := by
  by_contra hn
  have hn' : (p s).length < (q s).length := by omega
  let b : Bool := (q s)[(p s).length]
  have hx := (mem_brick_iff_get q (p.chart (fun _ => Stream'.const (!b)))).mp
    (h (chart_mem_brick p _)) s (p s).length hn'
  change (Stream'.appendStream' (p s) (Stream'.const (!b))).get (p s).length = b at hx
  rw [Stream'.get_append_length] at hx
  simp [Stream'.get,Stream'.const] at hx

lemma brick_injective : Function.Injective (brick : Prefix S → Set (Box S)) := by
  intro p q he
  have hl : ∀ s, (p s).length = (q s).length := fun s =>
    Nat.le_antisymm (length_le_of_brick_subset he.symm.subset s)
      (length_le_of_brick_subset he.subset s)
  let x := p.chart (fun _ _ => false)
  have hp := (mem_brick_iff p x).mp (chart_mem_brick p _)
  have hq := (mem_brick_iff q x).mp (he ▸ chart_mem_brick p _)
  apply Prefix.ext
  intro s
  exact (hp s).symm.trans ((congrArg (fun n => Stream'.take n (x s)) (hl s)).trans (hq s))

end TwistedBrin.Prefix

end

end OAI
