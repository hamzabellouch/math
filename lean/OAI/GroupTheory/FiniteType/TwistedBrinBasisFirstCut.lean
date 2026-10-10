import Mathlib
import OAI.GroupTheory.FiniteType.TwistedBrinPatternFactor

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
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

noncomputable def FirstCut {B C : Basis ρ} (h : CutRefines ρ B C) :=
  (b : B) × {s : S // s ∈ firstCuts ρ h b}
noncomputable instance {B C : Basis ρ} (h : CutRefines ρ B C) : Fintype (FirstCut ρ h) := by
  classical
  unfold FirstCut
  infer_instance

namespace CutSelections
variable {ρ} {B C : Basis ρ} (h : CutRefines ρ B C)
noncomputable def selected (K : CutSelections ρ h) : Finset (FirstCut ρ h) := by
  classical
  exact Finset.univ.filter (fun x => x.2.val ∈ K.val x.1)
lemma mem_selected (K : CutSelections ρ h) (x : FirstCut ρ h) :
    x ∈ selected h K ↔ x.2.val ∈ K.val x.1 := by
  classical
  simp [selected]

noncomputable def fromSelected (T : Finset (FirstCut ρ h)) : CutSelections ρ h := by
  classical
  refine ⟨fun b => (@Finset.filter {s : S // s ∈ firstCuts ρ h b}
    (fun s => (⟨b,s⟩ : FirstCut ρ h) ∈ T)
    (fun s => @Finset.decidableMem (FirstCut ρ h)
      (fun x y => Classical.propDecidable (x = y)) ⟨b,s⟩ T)
    Finset.univ).map (Function.Embedding.subtype _), ?_⟩
  intro b s hs
  obtain ⟨s',_,rfl⟩ := Finset.mem_map.mp hs
  exact s'.property

lemma mem_fromSelected (T : Finset (FirstCut ρ h)) (b : B) (s : S) :
    s ∈ (fromSelected h T).val b ↔ ∃ hs : s ∈ firstCuts ρ h b,
      (⟨b,⟨s,hs⟩⟩ : FirstCut ρ h) ∈ T := by
  classical
  simp only [fromSelected, Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,
    Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨s',hm,he⟩; subst s; exact ⟨s'.property,hm⟩
  · rintro ⟨hs,hm⟩; exact ⟨⟨s,hs⟩,hm,rfl⟩

lemma selected_fromSelected (T : Finset (FirstCut ρ h)) : selected h (fromSelected h T) = T := by
  classical
  ext x
  rw [mem_selected,mem_fromSelected]
  exact ⟨fun ⟨_,hh⟩ => hh,fun hh => ⟨x.2.property,hh⟩⟩

lemma fromSelected_selected (K : CutSelections ρ h) : fromSelected h (selected h K) = K := by
  apply Subtype.ext
  funext b
  apply Finset.ext
  intro s
  rw [mem_fromSelected]
  constructor
  · rintro ⟨hs,hm⟩
    exact (mem_selected h K ⟨b,⟨s,hs⟩⟩).mp hm
  · intro hm
    exact ⟨K.property b hm,(mem_selected h K _).mpr hm⟩

noncomputable def booleanEquiv : CutSelections ρ h ≃o Finset (FirstCut ρ h) where
  toFun := selected h
  invFun := fromSelected h
  left_inv := fromSelected_selected h
  right_inv := selected_fromSelected h
  map_rel_iff' := by
    intro K L
    change selected h K ⊆ selected h L ↔ ∀ b, K.val b ⊆ L.val b
    constructor
    · intro hh b s hs
      exact (mem_selected h L ⟨b,⟨s,K.property b hs⟩⟩).mp
        (hh ((mem_selected h K _).mpr hs))
    · intro hh x hx
      exact (mem_selected h L x).mpr (hh x.1 ((mem_selected h K x).mp hx))
end CutSelections

lemma grid_rank_bound (B : Basis ρ) (K : B → Finset S) :
    rank ρ (gridExpansion ρ B K) + 1 ≤ rank ρ B + 2 ^ (∑ b : B, (K b).card) := by
  classical
  have bound : ∀ (t : Finset B), (∑ b ∈ t, 2 ^ (K b).card) + 1 ≤
      t.card + 2 ^ (∑ b ∈ t, (K b).card) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert b t hb ih =>
      rw [Finset.sum_insert hb,Finset.sum_insert hb,Finset.card_insert_of_notMem hb,
        Nat.pow_add]
      have hp : 1 ≤ 2 ^ (K b).card := Nat.one_le_pow _ _ (by omega)
      have hq : 1 ≤ 2 ^ (∑ x ∈ t, (K x).card) := Nat.one_le_pow _ _ (by omega)
      nlinarith
  rw [rank_gridExpansion,rank_eq_card]
  simpa only [Finset.card_univ] using bound Finset.univ

end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

def ProperCutInterval (B C : Basis ρ) :=
  {D : CutInterval ρ B C // D.val ≠ B ∧ D.val ≠ C}
instance (B C : Basis ρ) : PartialOrder (ProperCutInterval ρ B C) :=
  inferInstanceAs (PartialOrder {D : CutInterval ρ B C // D.val ≠ B ∧ D.val ≠ C})

noncomputable def properCore {B C : Basis ρ} :
    ProperCutInterval ρ B C →o ProperCutInterval ρ B C where
  toFun D := ⟨D.val.core,D.val.core_ne_bottom D.property.1,D.val.core_ne_top D.property.2⟩
  monotone' := fun _ _ h => CutInterval.core_mono h
lemma properCore_le {B C : Basis ρ} (D : ProperCutInterval ρ B C) : properCore ρ D ≤ D :=
  D.val.core_le
@[simp] lemma properCore_idempotent {B C : Basis ρ} (D : ProperCutInterval ρ B C) :
    properCore ρ (properCore ρ D) = properCore ρ D :=
  Subtype.ext (D.val.core_core)

namespace CutSelections
variable {ρ} {B C : Basis ρ} (h : CutRefines ρ B C)
noncomputable def empty : CutSelections ρ h := ⟨fun _ => ∅,by simp⟩
noncomputable def full : CutSelections ρ h := ⟨firstCuts ρ h,fun _ _ hs => hs⟩
@[simp] lemma selected_empty : selected h (empty h) = ∅ := by
  classical
  ext x; simp [selected,empty]
@[simp] lemma selected_full : selected h (full h) = Finset.univ := by
  classical
  ext x; simp [selected,full]

lemma grid_eq_bottom_iff (K : CutSelections ρ h) :
    (toInterval h K).val = B ↔ selected h K = ∅ := by
  constructor
  · intro hk
    have he : K = empty h := Subtype.ext (gridExpansion_injective ρ B
      (hk.trans (gridExpansion_empty ρ B).symm))
    rw [he,selected_empty]
  · intro hk
    have he : K = empty h := (booleanEquiv h).injective (hk.trans (selected_empty h).symm)
    rw [he]
    exact gridExpansion_empty ρ B

lemma grid_eq_top_iff (htop : firstCore ρ h = C) (K : CutSelections ρ h) :
    (toInterval h K).val = C ↔ selected h K = Finset.univ := by
  constructor
  · intro hk
    have he : K = full h := Subtype.ext (gridExpansion_injective ρ B (hk.trans htop.symm))
    rw [he,selected_full]
  · intro hk
    have he : K = full h := (booleanEquiv h).injective (hk.trans (selected_full h).symm)
    rw [he]
    exact htop

lemma grid_ne_top (htop : firstCore ρ h ≠ C) (K : CutSelections ρ h) :
    (toInterval h K).val ≠ C := by
  intro hk
  apply htop
  have hK : CutRefines ρ (toInterval h K).val (firstCore ρ h) :=
    gridExpansion_mono ρ B K.val (firstCuts ρ h) K.property
  have hC : CutRefines ρ C (firstCore ρ h) := by simpa only [hk] using hK
  exact cutRefines_antisymm ρ (firstCore_upper ρ h) hC

def Proper := {K : CutSelections ρ h // (toInterval h K).val ≠ B ∧ (toInterval h K).val ≠ C}
instance : PartialOrder (Proper h) := inferInstanceAs
  (PartialOrder {K : CutSelections ρ h // (toInterval h K).val ≠ B ∧ (toInterval h K).val ≠ C})

noncomputable def properToInterval : Proper h →o ProperCutInterval ρ B C where
  toFun K := ⟨toInterval h K.val,K.property⟩
  monotone' := fun _ _ hk => to_mono h hk
noncomputable def properOfInterval : ProperCutInterval ρ B C →o Proper h where
  toFun D := ⟨ofInterval h D.val,by
    rw [to_of]
    exact ⟨D.val.core_ne_bottom D.property.1,D.val.core_ne_top D.property.2⟩⟩
  monotone' := fun _ _ hd => of_mono h hd
lemma proper_of_to (K : Proper h) : properOfInterval h (properToInterval h K) = K :=
  Subtype.ext (of_to h K.val)
lemma proper_to_of (D : ProperCutInterval ρ B C) :
    properToInterval h (properOfInterval h D) = properCore ρ D :=
  Subtype.ext (to_of h D.val)

noncomputable def properBooleanBoundary (htop : firstCore ρ h = C) :
    Proper h ≃o {T : Finset (FirstCut ρ h) // T ≠ ∅ ∧ T ≠ Finset.univ} where
  toFun K := ⟨selected h K.val,by
    exact ⟨fun he => K.property.1 ((grid_eq_bottom_iff h K.val).mpr he),
      fun he => K.property.2 ((grid_eq_top_iff h htop K.val).mpr he)⟩⟩
  invFun T := ⟨fromSelected h T.val,by
    exact ⟨fun he => T.property.1 ((selected_fromSelected h T.val).symm.trans
      ((grid_eq_bottom_iff h _).mp he)),
      fun he => T.property.2 ((selected_fromSelected h T.val).symm.trans
        ((grid_eq_top_iff h htop _).mp he))⟩⟩
  left_inv K := Subtype.ext (fromSelected_selected h K.val)
  right_inv T := Subtype.ext (selected_fromSelected h T.val)
  map_rel_iff' := (booleanEquiv h).map_rel_iff'

noncomputable def properBooleanFaces (htop : firstCore ρ h ≠ C) :
    Proper h ≃o {T : Finset (FirstCut ρ h) // T ≠ ∅} where
  toFun K := ⟨selected h K.val,fun he => K.property.1 ((grid_eq_bottom_iff h K.val).mpr he)⟩
  invFun T := ⟨fromSelected h T.val,
    (fun he => T.property ((selected_fromSelected h T.val).symm.trans
      ((grid_eq_bottom_iff h _).mp he))),grid_ne_top h htop _⟩
  left_inv K := Subtype.ext (fromSelected_selected h K.val)
  right_inv T := Subtype.ext (selected_fromSelected h T.val)
  map_rel_iff' := (booleanEquiv h).map_rel_iff'
end CutSelections
end TwistedBrin.Basis

namespace TwistedBrin.OrderNerve
section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Simplicial MonoidalCategory Opposite
variable {α β : Type u} [Preorder α] [Preorder β]

noncomputable def interpolation (f g : α →o β) (hfg : ∀ x, f x ≤ g x)
    {n : ℕ} (x : (nerve α) _⦋n⦌) (t : Δ[1] _⦋n⦌) : (nerve β) _⦋n⦌ := by
  classical
  refine (show Monotone (fun i => if t i = 0 then f (x.obj i) else g (x.obj i)) from ?_).functor
  intro i j hij
  have hx := x.monotone hij
  have ht := SSet.stdSimplex.monotone_apply t hij
  dsimp only at *
  split_ifs with hi hj hj
  · exact f.monotone hx
  · exact (f.monotone hx).trans (hfg _)
  · rw [hj] at ht
    exact (hi (le_antisymm ht (Fin.zero_le _))).elim
  · exact g.monotone hx

noncomputable def cylinder (f g : α →o β) (hfg : ∀ x, f x ≤ g x) :
    nerve α ⊗ Δ[1] ⟶ nerve β where
  app n := ↾fun z => interpolation f g hfg z.1 z.2
  naturality := by
    intro n m θ
    ext z i
    rfl

noncomputable def homotopy (f g : α →o β) (hfg : ∀ x, f x ≤ g x) :
    SSet.Homotopy (nerveMap f.toFunctor) (nerveMap g.toFunctor) where
  h := cylinder f g hfg
  h₀ := by
    ext n z i
    rcases n with ⟨⟨n⟩⟩
    change (if (0 : Fin 2) = 0 then f (z.obj i) else g (z.obj i)) = f (z.obj i)
    simp
  h₁ := by
    ext n z i
    rcases n with ⟨⟨n⟩⟩
    change (if (1 : Fin 2) = 0 then f (z.obj i) else g (z.obj i)) = g (z.obj i)
    simp

  rel := by
    ext n z
    exact (show False from z.1.property).elim

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory
universe w
variable {α β : Type u} [Preorder α] [Preorder β]

@[simp] lemma nerveMap_order_id : nerveMap (OrderHom.id : α →o α).toFunctor = 𝟙 _ := rfl
@[simp] lemma nerveMap_order_comp {γ : Type u} [Preorder γ]
    (f : α →o β) (g : β →o γ) :
    nerveMap (g.comp f).toFunctor = nerveMap f.toFunctor ≫ nerveMap g.toFunctor := rfl

noncomputable def retractionChainEquiv
    {C : Type w} [Category.{v} C] [Preadditive C] [Limits.HasCoproducts.{u} C]
    (i : β →o α) (r : α →o β) (hri : ∀ x, r (i x) = x)
    (hir : ∀ x, i (r x) ≤ x) (R : C) :
    HomotopyEquiv ((nerve α).chainComplex R) ((nerve β).chainComplex R) where
  hom := SSet.chainComplexMap (nerveMap r.toFunctor) R
  inv := SSet.chainComplexMap (nerveMap i.toFunctor) R
  homotopyHomInvId := by
    have H := (homotopy (i.comp r) OrderHom.id hir).chainComplexMap R
    simpa only [nerveMap_order_comp,nerveMap_order_id,SSet.chainComplexMap,CategoryTheory.Functor.map_comp,CategoryTheory.Functor.map_id] using H
  homotopyInvHomId := by
    apply Homotopy.ofEq
    have hr : r.comp i = OrderHom.id := by ext x; exact hri x
    change ((SSet.chainComplexFunctor C).obj R).map _ ≫
      ((SSet.chainComplexFunctor C).obj R).map _ = _
    rw [← CategoryTheory.Functor.map_comp,← nerveMap_order_comp,hr,nerveMap_order_id,CategoryTheory.Functor.map_id]
end TwistedBrin.OrderNerve

namespace TwistedBrin.Basis
section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable {A S : Type u} [Group A] (ρ : A →* Equiv.Perm S)

noncomputable def properIntervalChainEquiv {B C : Basis ρ}
    (h : CutRefines ρ B C) (R : ModuleCat.{u} ℤ) :
    HomotopyEquiv ((nerve (ProperCutInterval ρ B C)).chainComplex R)
      ((nerve (CutSelections.Proper h)).chainComplex R) :=
  OrderNerve.retractionChainEquiv
    (CutSelections.properToInterval h) (CutSelections.properOfInterval h)
    (CutSelections.proper_of_to h)
    (fun D => by rw [CutSelections.proper_to_of]; exact properCore_le ρ D) R

end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

def Elementary (B C : Basis ρ) : Prop :=
  ∃ (K : B → Finset S), gridExpansion ρ B K = C

lemma elementary_iff_firstCore {B C : Basis ρ} (h : CutRefines ρ B C) :
    Elementary ρ B C ↔ firstCore ρ h = C := by
  constructor
  · rintro ⟨K,rfl⟩
    exact firstCore_grid ρ B K h
  · intro hh
    exact ⟨firstCuts ρ h,hh⟩

lemma elementary_refl (B : Basis ρ) : Elementary ρ B B :=
  ⟨fun _ => ∅,gridExpansion_empty ρ B⟩

lemma elementary_cutRefines {B C : Basis ρ} (h : Elementary ρ B C) : CutRefines ρ B C := by
  obtain ⟨K,rfl⟩ := h
  exact cutRefines_gridExpansion ρ B K
end TwistedBrin.Basis

namespace TwistedBrin.Pattern
variable {S : Type u}

def FullGrid (P : Pattern S) : Prop :=
  (∀ i j : Leaves P, ∀ s, (leafPrefix P i s).length = (leafPrefix P j s).length) ∧
  (∀ i : Leaves P, ∀ s, (leafPrefix P i s).length ≤ 1)

lemma fullGrid_uniform (K : Finset S) : FullGrid (uniform K.toList) := by
  classical
  constructor
  · intro i j s
    rw [uniform_length,uniform_length]
  · intro i s
    rw [uniform_length]
    exact List.nodup_iff_count_le_one.mp K.nodup_toList s

lemma FullGrid.of_pieces_eq {P Q : Pattern S} (hQ : FullGrid Q) (he : pieces P = pieces Q) :
    FullGrid P := by
  have existsLeaf (i : Leaves P) : ∃ j : Leaves Q, leafPrefix Q j = leafPrefix P i := by
    apply (mem_pieces Q _).mp
    rw [← he]
    exact (mem_pieces P _).mpr ⟨i,rfl⟩
  constructor
  · intro i j s
    obtain ⟨i',hi⟩ := existsLeaf i
    obtain ⟨j',hj⟩ := existsLeaf j
    rw [← hi,← hj]
    exact hQ.1 i' j' s
  · intro i s
    obtain ⟨j,hj⟩ := existsLeaf i
    rw [← hj]
    exact hQ.2 j s

open Classical in
lemma FullGrid.length_eq {P : Pattern S} (h : FullGrid P) (i : Leaves P) (s : S) :
    (leafPrefix P i s).length = if s ∈ firstCoordinates P then 1 else 0 := by
  classical
  split_ifs with hs
  · have hp := List.length_pos_iff.mpr ((mem_firstCoordinates P s).mp hs i)
    have hq := h.2 i s
    omega
  · have hz : leafPrefix P i s = [] := by
      by_contra hn
      apply hs
      apply (mem_firstCoordinates P s).mpr
      intro j
      have hi := List.length_pos_iff.mpr hn
      have hj := h.1 i j s
      exact List.length_pos_iff.mp (by omega)
    rw [hz]
    rfl

lemma pieces_eq_of_lengths {P Q : Pattern S}
    (hl : ∀ (i : Leaves P) (j : Leaves Q) s,
      (leafPrefix P i s).length = (leafPrefix Q j s).length) : pieces P = pieces Q := by
  classical
  have help (P Q : Pattern S)
      (hl : ∀ (i : Leaves P) (j : Leaves Q) s,
        (leafPrefix P i s).length = (leafPrefix Q j s).length) : pieces P ⊆ pieces Q := by
    intro p hp
    obtain ⟨i,rfl⟩ := (mem_pieces P p).mp hp
    let x : Box S := (leafPrefix P i).chart (fun _ _ => false)
    have hx : x ∈ (leafPrefix P i).brick := Prefix.chart_mem_brick _ _
    obtain ⟨j,hj,_⟩ := partition Q x
    exact (mem_pieces Q _).mpr ⟨j,Prefix.eq_of_mem_of_length_eq hj hx (fun s => (hl i j s).symm)⟩
  exact Finset.Subset.antisymm (help P Q hl) (help Q P (fun j i s => (hl i j s).symm))

lemma FullGrid.pieces_eq_uniform {P : Pattern S} (h : FullGrid P) :
    pieces P = pieces (uniform (firstCoordinates P).toList) := by
  classical
  apply pieces_eq_of_lengths
  intro i j s
  rw [h.length_eq,uniform_length]
  split_ifs with hs
  · exact (List.nodup_iff_count_eq_one.mp (firstCoordinates P).nodup_toList s
      (Finset.mem_toList.mpr hs)).symm
  · exact (List.count_eq_zero.mpr (by simpa using hs)).symm

lemma FullGrid.graft_part {P : Pattern S} {Q : Leaves P → Pattern S}
    (h : FullGrid (graft P Q)) (i : Leaves P) : FullGrid (Q i) := by
  constructor
  · intro j k s
    have he := h.1 (graftLeaves P Q ⟨i,j⟩) (graftLeaves P Q ⟨i,k⟩) s
    rw [graft_prefix,graft_prefix] at he
    simpa only [Prefix.append_apply,List.length_append,Nat.add_left_cancel_iff] using he
  · intro j s
    have he := h.2 (graftLeaves P Q ⟨i,j⟩) s
    rw [graft_prefix] at he
    simp only [Prefix.append_apply,List.length_append] at he
    omega

lemma FullGrid.of_relabel {P : Pattern S} {σ : Equiv.Perm S}
    (h : FullGrid (relabel σ P)) : FullGrid P := by
  constructor
  · intro i j s
    have he := h.1 (relabelLeaves σ P i) (relabelLeaves σ P j) (σ s)
    simpa only [relabel_prefix,Prefix.permute_apply,Equiv.symm_apply_apply] using he
  · intro i s
    have he := h.2 (relabelLeaves σ P i) (σ s)
    simpa only [relabel_prefix,Prefix.permute_apply,Equiv.symm_apply_apply] using he
end TwistedBrin.Pattern

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma expand_eq_of_pattern_pieces_eq (B : Basis ρ) (P Q : B → Pattern S)
    (h : ∀ b, Pattern.pieces (P b) = Pattern.pieces (Q b)) : expand ρ B P = expand ρ B Q := by
  classical
  have help (P Q : B → Pattern S)
      (h : ∀ b, Pattern.pieces (P b) = Pattern.pieces (Q b)) :
      (expand ρ B P).pieces ⊆ (expand ρ B Q).pieces := by
    intro g hg
    obtain ⟨⟨b,i⟩,_,rfl⟩ := Finset.mem_image.mp hg
    have hp : Pattern.leafPrefix (P b) i ∈ Pattern.pieces (Q b) := by
      rw [← h b]
      exact (Pattern.mem_pieces _ _).mpr ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := (Pattern.mem_pieces _ _).mp hp
    apply Finset.mem_image.mpr
    refine ⟨⟨b,j⟩,Finset.mem_univ _,?_⟩
    change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B b)
      (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (Q b) j))) = _
    rw [hj]
    rfl
  exact Basis.ext ρ (Finset.Subset.antisymm (help P Q h) (help Q P (fun b => (h b).symm)))

lemma Forest.elementary_of_fullGrid {B C : Basis ρ} (F : Forest ρ B C)
    (h : ∀ b, Pattern.FullGrid (F.pattern b)) : Elementary ρ B C := by
  refine ⟨fun b => Pattern.firstCoordinates (F.pattern b),?_⟩
  exact (expand_eq_of_pattern_pieces_eq ρ B _ _ (fun b => (h b).pieces_eq_uniform.symm)).trans
    (F.expand_eq ρ)

lemma Forest.fullGrid_of_elementary {B C : Basis ρ} (F : Forest ρ B C)
    (h : Elementary ρ B C) (b : B) : Pattern.FullGrid (F.pattern b) := by
  obtain ⟨K,rfl⟩ := h
  exact (Pattern.fullGrid_uniform (K b)).of_pieces_eq
    (F.pieces_eq ρ (Forest.expansion B (fun b => Pattern.uniform (K b).toList)) b)

lemma elementary_upper {B C D : Basis ρ} (hBC : CutRefines ρ B C)
    (hCD : CutRefines ρ C D) (hBD : Elementary ρ B D) : Elementary ρ C D := by
  obtain ⟨F⟩ := hBC
  obtain ⟨K⟩ := hCD
  apply K.elementary_of_fullGrid ρ
  intro c
  obtain ⟨⟨b,i⟩,rfl⟩ := F.leaves.surjective c
  have hh := (F.trans K).fullGrid_of_elementary ρ hBD b
  exact (hh.graft_part i).of_relabel
end TwistedBrin.Basis

end

end OAI
