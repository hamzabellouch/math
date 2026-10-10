import Mathlib
import OAI.Geometry.Borsuk.Simplicial.LinearMapSupport
import OAI.Geometry.Borsuk.Simplicial.DoubleEraseSumFun

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

lemma contigSimplex_boundary (L : PreAbstractSimplicialComplex W) (f g : V → W)
    {s : Finset V} (hs : s.image f ∪ s.image g ∈ L) :
    boundary L (contigSimplex L f g s) =
      mapSimplex L f s + mapSimplex L g s + ∑ a ∈ s, contigSimplex L f g (s.erase a) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hn : s.Nonempty := by
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      have hs' : (∅ : Finset W) ∈ L := by simpa [he] using hs
      simpa using (L.isRelLowerSet_faces hs').1
    have hf : s.image f ∈ L := (L.isRelLowerSet_faces hs).2 Finset.subset_union_left (hn.image f)
    have hg : s.image g ∈ L := (L.isRelLowerSet_faces hs).2 Finset.subset_union_right (hn.image g)
    have hb : f hn.choose ∈ s.image f ∪ s.image g :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem f hn.choose_spec)
    let z := mapSimplex L f s + mapSimplex L g s + ∑ a ∈ s, contigSimplex L f g (s.erase a)
    have hi (a : V) (ha : a ∈ s) : boundary L (contigSimplex L f g (s.erase a)) =
        mapSimplex L f (s.erase a) + mapSimplex L g (s.erase a) +
          ∑ b ∈ s.erase a, contigSimplex L f g ((s.erase a).erase b) := by
      rcases (s.erase a).eq_empty_or_nonempty with he | hne
      · simp [he, mapSimplex]
      · apply ih (s.erase a) (Finset.erase_ssubset ha)
        apply (L.isRelLowerSet_faces hs).2
        · exact Finset.union_subset_union (Finset.image_subset_image (Finset.erase_subset a s))
            (Finset.image_subset_image (Finset.erase_subset a s))
        · exact (hne.image f).mono Finset.subset_union_left
    have hzbd : boundary L z = 0 := by
      simp only [z, map_add, map_sum, mapSimplex_boundary L f hf, mapSimplex_boundary L g hg]
      rw [Finset.sum_congr rfl hi]
      simp only [Finset.sum_add_distrib]
      rw [double_erase_sum_fun, add_zero]
      exact chain_add_self L _
    have hzaug : augmentation L z = 0 := by
      simp only [z, map_add, map_sum, mapSimplex_augmentation L f hf,
        mapSimplex_augmentation L g hg, contigSimplex_augmentation, Finset.sum_const_zero, add_zero]
      exact CharTwo.add_self_eq_zero _
    have hzcone : ∀ t ∈ z.support, insert (f hn.choose) t.val ∈ L := by
      intro t ht
      apply (L.isRelLowerSet_faces hs).2 _ (Finset.insert_nonempty _ _)
      apply Finset.insert_subset hb
      rcases Finset.mem_union.mp (Finsupp.support_add ht) with ht | ht
      · rcases Finset.mem_union.mp (Finsupp.support_add ht) with htf | htg
        · rw [support_mapSimplex L f s htf]; exact Finset.subset_union_left
        · rw [support_mapSimplex L g s htg]; exact Finset.subset_union_right
      · obtain ⟨a,ha,hta⟩ := support_sum_chains L s _ ht
        exact (contigSimplex_carrier L f g (s.erase a) hta).trans
          (Finset.union_subset_union (Finset.image_subset_image (Finset.erase_subset a s))
            (Finset.image_subset_image (Finset.erase_subset a s)))
    rw [contigSimplex_nonempty L f g hn]
    change boundary L (cone L (f hn.choose) z) = z
    rw [cone_boundary L _ z hzcone, hzbd, hzaug, map_zero, zero_smul, add_zero, add_zero]

noncomputable def contigMap (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f g : V → W) : Chain K →ₗ[F₂] Chain L :=
  Finsupp.linearCombination F₂ (fun s => contigSimplex L f g s.val)

lemma contigMap_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f g : V → W) {s : Finset V} (hs : s ∈ K) :
    contigMap K L f g (simplex K s) = contigSimplex L f g s := by
  simp [simplex_of_mem K hs, contigMap, Finsupp.linearCombination_single]

lemma contigMap_simplex_subset (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f g : V → W) {s t : Finset V}
    (ht : t ∈ K) (hs : s ⊆ t) :
    contigMap K L f g (simplex K s) = contigSimplex L f g s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact contigMap_simplex K L f g ((K.isRelLowerSet_faces ht).2 hs hn)

lemma contigMap_degree (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f g : V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L (d+1)).comap (contigMap K L f g) := by
  apply grade_map K L _ d (d+1)
  intro s hs hd
  rw [contigMap_simplex K L f g hs, ← hd]
  exact contigSimplex_degree L f g s

lemma contigMap_boundary_of_support (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f g : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∪ s.val.image g ∈ L) :
    boundary L (contigMap K L f g c) = mapChains K L f c + mapChains K L g c +
      contigMap K L f g (boundary K c) := by
  let A : Chain K →ₗ[F₂] Chain L :=
    mapChains K L f + mapChains K L g + (contigMap K L f g).comp (boundary K)
  change ((boundary L).comp (contigMap K L f g)) c = A c
  apply linearMap_eq_of_support
  intro s hs
  simp only [LinearMap.comp_apply, A, LinearMap.add_apply]
  rw [contigMap_simplex K L f g s.property, contigSimplex_boundary L f g (hc s hs),
    mapChains_simplex K L f s.property, mapChains_simplex K L g s.property,
    boundary_simplex K s.property, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact (contigMap_simplex_subset K L f g s.property (Finset.erase_subset a s.val)).symm

lemma contig_maps_agree_top (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f g : V → W) (d : ℕ) (c : Chain K)
    (hc : c ∈ degreeChains K d) (hbd : boundary K c = 0)
    (hfg : ∀ s ∈ c.support, s.val.image f ∪ s.val.image g ∈ L)
    (hL : ∀ s ∈ L, s.card ≤ d) : mapChains K L f c = mapChains K L g c := by
  have hh : contigMap K L f g c = 0 := by
    have ht := contigMap_degree K L f g d hc
    rw [degreeChains_eq_bot_of_card_bound L (d+1) (fun s hs => by have := hL s hs; omega)] at ht
    exact ht
  have he := contigMap_boundary_of_support K L f g c hfg
  rw [hh, map_zero, hbd, map_zero, add_zero] at he
  have h := eq_neg_of_add_eq_zero_left he.symm
  have hn : -(mapChains K L g c) = mapChains K L g c := by
    ext s
    exact CharTwo.neg_eq _
  exact h.trans hn

end BorsukNine.SimplicialChains

end OAI
