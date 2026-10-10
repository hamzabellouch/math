import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.TemplateRelators
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PrivateBankWord

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

structure PrivateRoutingBank {m : ℕ} (i : Fin 5 → Fin m) where
  row : Fin 5 → Fin 5 ↪ Fin m
  source : ∀ j, row j 0=i j
  fresh : ∀ j k, k≠0 → ∀ l, row j k≠i l
  separate : ∀ j k j' k', k≠0 → k'≠0 → row j k=row j' k' → j=j' ∧ k=k'

namespace PrivateRoutingBank
variable {m : ℕ} {i : Fin 5 → Fin m} (P : PrivateRoutingBank i)

def target : Fin 5 ↪ Fin m :=
  ⟨fun j => P.row j 1,fun _ _ he => (P.separate _ _ _ _ (by decide) (by decide) he).1⟩

noncomputable def alphabet : Finset (Fin m) :=
  Finset.univ.image (fun p : Fin 5 × Fin 5 => P.row p.1 p.2)

theorem alphabet_card : P.alphabet.card ≤ 25 := by
  classical
  exact (Finset.card_image_le).trans (by simp)

theorem row_subset (j : Fin 5) : orderedTrackAlphabet (P.row j) ⊆ P.alphabet := by
  classical
  intro t ht
  obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp ht
  exact Finset.mem_image.mpr ⟨(j,k),Finset.mem_univ _,rfl⟩

theorem source_mem (j : Fin 5) : i j ∈ P.alphabet := by
  rw [← P.source j]
  exact P.row_subset j (orderedTrackAlphabet_mem _ _)

theorem target_other_notmem (j l : Fin 5) (hjl : j≠l) :
    P.target l ∉ orderedTrackAlphabet (P.row j) := by
  intro ht
  obtain ⟨k,_,he⟩ := Finset.mem_map.mp ht
  by_cases hk : k=0
  · subst k
    rw [P.source j] at he
    exact P.fresh l 1 (by decide) j he.symm
  · exact hjl (P.separate j k l 1 hk (by decide) he).1

theorem source_other_frame_notmem {a : ℕ} (V : polygonAlgebra a)
    (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a m V (fun j => (i j,u j))))
    (j l : Fin 5) (hjl : j≠l) (x : V.val) :
    (i l,translate a (u l) x.val) ∉
      frameDomain (orderedTrackAlphabet (P.row j)) (fun _ => u j) V := by
  rintro ⟨t,ht,y,hy,he⟩
  obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp ht
  have ht := congrArg Prod.fst he
  by_cases hk : k=0
  · subst k
    rw [P.source j] at he
    have hh : SlotMap a m V (fun j => (i j,u j)) (j,⟨y,hy⟩) =
        SlotMap a m V (fun j => (i j,u j)) (l,x) := he.symm
    exact hjl (congrArg Prod.fst (hinj hh))
  · exact P.fresh j k hk l ht.symm

end PrivateRoutingBank

theorem exists_privateRoutingBank {m : ℕ} (i : Fin 5 → Fin m) (J : Finset (Fin m))
    (hreserve : 20 ≤ ((Finset.univ : Finset (Fin m)) \
      (J ∪ Finset.univ.image i)).card) :
    ∃ P : PrivateRoutingBank i, ∀ j k, k≠0 → P.row j k ∉ J := by
  classical
  let R := (Finset.univ : Finset (Fin m)) \ (J ∪ Finset.univ.image i)
  have hc : Fintype.card (Fin 5 × {k : Fin 5 // k≠0}) ≤ Fintype.card R := by
    have hfour : Fintype.card {k : Fin 5 // k≠0}=4 := by decide
    rw [Fintype.card_prod,Fintype.card_fin,hfour,Fintype.card_coe]
    exact hreserve
  obtain ⟨p⟩ := Function.Embedding.nonempty_of_card_le hc
  let f : Fin 5 → Fin 5 → Fin m := fun j k =>
    if hk : k=0 then i j else (p (j,⟨k,hk⟩)).val
  have hfresh : ∀ j k hk l, (p (j,⟨k,hk⟩)).val ≠ i l := by
    intro j k hk l he
    exact (Finset.mem_sdiff.mp (p (j,⟨k,hk⟩)).property).2
      (Finset.mem_union_right _ (he.symm ▸ Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩))
  have hinj : ∀ j, Function.Injective (f j) := by
    intro j k l he
    by_cases hk : k=0 <;> by_cases hl : l=0
    · exact hk.trans hl.symm
    · subst k
      have hh : i j=(p (j,⟨l,hl⟩)).val := by simpa [f,hl] using he
      exact (hfresh j l hl j hh.symm).elim
    · subst l
      have hh : (p (j,⟨k,hk⟩)).val=i j := by simpa [f,hk] using he
      exact (hfresh j k hk j hh).elim
    · have he' : p (j,⟨k,hk⟩)=p (j,⟨l,hl⟩) :=
        Subtype.ext (by simpa only [f,dite_eq_right hk,dite_eq_right hl] using he)
      have hh := p.injective he'
      exact congrArg (fun q : Fin 5 × {k : Fin 5 // k≠0} => q.2.val) hh
  let P : PrivateRoutingBank i := {
    row := fun j => ⟨f j,hinj j⟩
    source := by intro j; simp [f]
    fresh := by
      intro j k hk l
      exact (show f j k≠i l from by simpa [f,hk] using hfresh j k hk l)
    separate := by
      intro j k j' k' hk hk' he
      change f j k=f j' k' at he
      have he' : p (j,⟨k,hk⟩)=p (j',⟨k',hk'⟩) :=
        Subtype.ext (by simpa only [f,dite_eq_right hk,dite_eq_right hk'] using he)
      have hh := p.injective he'
      exact ⟨congrArg Prod.fst hh,congrArg (fun q : Fin 5 × {k : Fin 5 // k≠0} => q.2.val) hh⟩ }
  refine ⟨P,?_⟩
  intro j k hk hJ
  have hh : (p (j,⟨k,hk⟩)).val ∈ J := by simpa [P,f,hk] using hJ
  exact (Finset.mem_sdiff.mp (p (j,⟨k,hk⟩)).property).2 (Finset.mem_union_left _ hh)

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

noncomputable def privateRoutingFactor (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing) (P : PrivateRoutingBank i)
    (b : Fin (m+1)) (hb : b ∉ P.alphabet) (V : polygonAlgebra a) (j : Fin 5) :
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.distinctSlotStar hlarge h hr (P.row j) (fun _ => u j)
    (balancedOffsetFrame a r m hm (orderedTrackAlphabet (P.row j)) b
      (fun ht => hb (P.row_subset j ht)) (fun _ => u j)) V privateCycleStar

noncomputable def privateRoutingWord (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing) (P : PrivateRoutingBank i)
    (b : Fin (m+1)) (hb : b ∉ P.alphabet) (V : polygonAlgebra a) :
    BoundedRelationCover M (alternatingGenerator a r m hm) :=
  ((List.finRange 5).map (B.privateRoutingFactor hlarge h hr i u P b hb V)).prod

theorem privateRoutingWord_properties (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (P : PrivateRoutingBank i) (b : Fin (m+1)) (hb : b ∉ P.alphabet)
    (V : polygonAlgebra a)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    B.privateRoutingWord hlarge h hr i u P b hb V ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range ∧
      B.privateRoutingWord hlarge h hr i u P b hb V ∈ sourceAlignedGroup a r m hm M B.t P.alphabet ∧
      ∀ (j : Fin 5) (x : V.val),
        (coverMap M (alternatingGenerator a r m hm) (B.privateRoutingWord hlarge h hr i u P b hb V)).val.val (i j,translate a (u j) x.val) =
          (P.target j,translate a (u j) x.val) := by
  classical
  have hbrow (j : Fin 5) : b ∉ orderedTrackAlphabet (P.row j) :=
    fun ht => hb (P.row_subset j ht)
  let F (j : Fin 5) := balancedOffsetFrame a r m hm (orderedTrackAlphabet (P.row j))
    b (hbrow j) (fun _ => u j)
  let g : Fin 5 → BoundedRelationCover M (alternatingGenerator a r m hm) := fun j =>
    B.distinctSlotStar hlarge h hr (P.row j) (fun _ => u j) (F j) V privateCycleStar
  let l := List.finRange 5
  let w := (l.map g).prod
  change w ∈ _ ∧ w ∈ _ ∧ _
  refine ⟨?_,?_,?_⟩
  · apply Subgroup.list_prod_mem
    intro t ht
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    exact B.distinctSlotStar_uniform_mem hlarge h hr (P.row j) b (hbrow j)
      (fun _ => u j) (F j) (u j) (fun _ => rfl) V privateCycleStar
  · apply Subgroup.list_prod_mem
    intro t ht
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    exact sourceAlignedGroup_mono B.t (P.row_subset j)
      (B.frameStar_alphabet_mem hlarge h hr (orderedTrackAlphabet (P.row j))
        (by simp [orderedTrackAlphabet]) b (hbrow j) (fun _ => u j) (F j) V
        (universalMap (orderedTrackHom (P.row j)) privateCycleStar))
  · intro j x
    let q : BoundedRelationCover M (alternatingGenerator a r m hm) →* Equiv.Perm (TrackPoint a (m+1)) :=
      (polygonFullGroup a (m+1)).subtype.comp
        ((polygonAlternatingGroup a (m+1)).subtype.comp (coverMap M (alternatingGenerator a r m hm)))
    change q w (i j,translate a (u j) x.val) = _
    change q ((l.map g).prod) _ = _
    rw [map_list_prod,List.map_map]
    apply perm_list_prod_transport l (List.nodup_finRange 5) (fun k => q (g k)) j (by simp [l])
    · have he := B.distinctSlotStar_apply hlarge h hr (P.row j) (fun _ => u j)
        (F j) V privateCycleStar 0 x
      rw [privateCycleStar_projection,privateCycle_apply_zero,P.source j] at he
      exact he
    · intro k hk hkj
      constructor
      · exact B.frameStar_supported hlarge h hr _ (fun _ => u k) (F k) V
          (universalMap (orderedTrackHom (P.row k)) privateCycleStar) _
          (P.source_other_frame_notmem V u hinj k j hkj x)
      · apply B.frameStar_supported hlarge h hr _ (fun _ => u k) (F k) V
          (universalMap (orderedTrackHom (P.row k)) privateCycleStar)
        rintro ⟨t,ht,y,hy,he⟩
        have hte : P.target j=t := congrArg Prod.fst he
        exact P.target_other_notmem k j hkj (hte.symm ▸ ht)

theorem repeated_bank_routing (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (P : PrivateRoutingBank i) (b : Fin (m+1)) (hb : b ∉ P.alphabet)
    (V : polygonAlgebra a)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    ∃ w : BoundedRelationCover M (alternatingGenerator a r m hm),
      w ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range ∧
      w ∈ sourceAlignedGroup a r m hm M B.t P.alphabet ∧
      ∀ (j : Fin 5) (x : V.val),
        (coverMap M (alternatingGenerator a r m hm) w).val.val (i j,translate a (u j) x.val) =
          (P.target j,translate a (u j) x.val) :=
  ⟨B.privateRoutingWord hlarge h hr i u P b hb V,
    B.privateRoutingWord_properties hlarge h hr i u P b hb V hinj⟩

end InitialCoverSystem

end SimpleAmenable

end OAI
