import Mathlib
import OAI.Geometry.Borsuk.Simplicial.SimplexMemDegreeAll

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq W] in
lemma double_erase_sum_fun (L : PreAbstractSimplicialComplex W) (H : Finset V → Chain L)
    (s : Finset V) : (∑ a ∈ s, ∑ b ∈ s.erase a, H ((s.erase a).erase b)) = 0 := by
  classical
  let g (p : V × V) : Chain L := if p.1 = p.2 then 0 else H ((s.erase p.1).erase p.2)
  have hg : (∑ a ∈ s, ∑ b ∈ s.erase a, H ((s.erase a).erase b)) =
      ∑ p ∈ s ×ˢ s, g p := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.filter_ne, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b <;> simp [g, hab, Finset.filter_ne]
  rw [hg]
  apply Finset.sum_involution (fun p _ => p.swap)
  · intro p _
    dsimp [g]
    by_cases he : p.1 = p.2
    · simp [he]
    · simp only [he, ite_false, Ne.symm he, Finset.erase_right_comm]
      exact chain_add_self L _
  · intro p _ hg he
    have h : p.1 = p.2 := congrArg Prod.snd he
    exact hg (by simp [g, h])
  · intro p _; exact Prod.swap_swap p
  · intro p hp; exact Finset.mem_product.mpr (And.symm (Finset.mem_product.mp hp))

omit [DecidableEq V] in
lemma support_mapSimplex (L : PreAbstractSimplicialComplex W) (f : V → W)
    (s : Finset V) {t : {t : Finset W // t ∈ L}}
    (ht : t ∈ (mapSimplex L f s).support) : t.val = s.image f := by
  unfold mapSimplex at ht
  split_ifs at ht
  · exact (mem_support_simplex L _ t).mp ht
  · simp at ht

omit [DecidableEq V] in
lemma mapSimplex_degree (L : PreAbstractSimplicialComplex W) (f : V → W) (s : Finset V) :
    mapSimplex L f s ∈ degreeChains L s.card := by
  unfold mapSimplex
  split_ifs with h
  · rw [← h]; exact simplex_mem_degree_all L _
  · exact Submodule.zero_mem _

lemma mapSimplex_boundary (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s.image f ∈ L) :
    boundary L (mapSimplex L f s) = ∑ a ∈ s, mapSimplex L f (s.erase a) := by
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hinj), boundary_simplex L hs,
      Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr (hinj.mono (Finset.erase_subset a s))),
        image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, ite_eq_right (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]

omit [DecidableEq V] in
lemma mapSimplex_augmentation (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s.image f ∈ L) :
    augmentation L (mapSimplex L f s) = if s.card = 1 then 1 else 0 := by
  by_cases hinj : (s.image f).card = s.card
  · rw [mapSimplex, ite_eq_left hinj, augmentation_simplex L hs, hinj]
  · have hc : s.card ≠ 1 := by
      intro h
      obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp h
      simp at hinj
    simp [mapSimplex, hinj, hc]

noncomputable def contigSimplex (L : PreAbstractSimplicialComplex W) (f g : V → W)
    (s : Finset V) : Chain L :=
  if hs : s.Nonempty then
    cone L (f hs.choose) (mapSimplex L f s + mapSimplex L g s +
      ∑ a ∈ s.attach, contigSimplex L f g (s.erase a.val))
  else 0
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem a.property

@[simp] lemma contigSimplex_empty (L : PreAbstractSimplicialComplex W) (f g : V → W) :
    contigSimplex L f g ∅ = 0 := by rw [contigSimplex]; simp

lemma contigSimplex_nonempty (L : PreAbstractSimplicialComplex W) (f g : V → W)
    {s : Finset V} (hs : s.Nonempty) :
    contigSimplex L f g s = cone L (f hs.choose)
      (mapSimplex L f s + mapSimplex L g s + ∑ a ∈ s, contigSimplex L f g (s.erase a)) := by
  rw [contigSimplex, dite_eq_left hs]
  exact congrArg (fun z => cone L (f hs.choose) (mapSimplex L f s + mapSimplex L g s + z))
    (Finset.sum_attach s (fun a : V => contigSimplex L f g (s.erase a)))

lemma contigSimplex_carrier (L : PreAbstractSimplicialComplex W) (f g : V → W)
    (s : Finset V) {t : {t : Finset W // t ∈ L}}
    (ht : t ∈ (contigSimplex L f g s).support) : t.val ⊆ s.image f ∪ s.image g := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp at ht
    rw [contigSimplex_nonempty L f g hs] at ht
    obtain ⟨u,hu,_,htu⟩ := support_cone L _ _ ht
    rw [htu]
    apply Finset.insert_subset
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem f hs.choose_spec)
    have hsub : ∀ a ∈ s, (s.erase a).image f ∪ (s.erase a).image g ⊆ s.image f ∪ s.image g := by
      intro a _
      exact Finset.union_subset_union (Finset.image_subset_image (Finset.erase_subset a s))
        (Finset.image_subset_image (Finset.erase_subset a s))
    rcases Finset.mem_union.mp (Finsupp.support_add hu) with hu | hu
    · rcases Finset.mem_union.mp (Finsupp.support_add hu) with hf | hg
      · rw [support_mapSimplex L f s hf]; exact Finset.subset_union_left
      · rw [support_mapSimplex L g s hg]; exact Finset.subset_union_right
    · obtain ⟨a,ha,hua⟩ := support_sum_chains L s _ hu
      exact (ih (s.erase a) (Finset.erase_ssubset ha) hua).trans (hsub a ha)

lemma contigSimplex_degree (L : PreAbstractSimplicialComplex W) (f g : V → W)
    (s : Finset V) : contigSimplex L f g s ∈ degreeChains L (s.card+1) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · rw [contigSimplex_empty]; exact Submodule.zero_mem _
    rw [contigSimplex_nonempty L f g hs]
    apply cone_degree L _ s.card
    apply Submodule.add_mem _
    · exact Submodule.add_mem _ (mapSimplex_degree L f s) (mapSimplex_degree L g s)
    · apply Submodule.sum_mem
      intro a ha
      have h := ih (s.erase a) (Finset.erase_ssubset ha)
      simpa only [Finset.card_erase_of_mem ha, Nat.sub_add_cancel hs.card_pos] using h

lemma contigSimplex_augmentation (L : PreAbstractSimplicialComplex W) (f g : V → W)
    (s : Finset V) : augmentation L (contigSimplex L f g s) = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  exact augmentation_eq_zero_of_degree L (s.card+1) (by have := hs.card_pos; omega)
    (contigSimplex_degree L f g s)

end BorsukNine.SimplicialChains

end OAI
