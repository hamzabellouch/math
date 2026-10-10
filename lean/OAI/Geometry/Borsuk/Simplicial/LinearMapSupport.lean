import Mathlib
import OAI.Geometry.Borsuk.Simplicial.MapChainsEquivSimplexAll

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma linearMap_eq_of_support {K : PreAbstractSimplicialComplex V}
    {M : Type*} [AddCommMonoid M] [Module F₂ M]
    (T U : Chain K →ₗ[F₂] M) (c : Chain K)
    (hc : ∀ s ∈ c.support, T (simplex K s.val) = U (simplex K s.val)) : T c = U c := by
  rw [chain_eq_sum K c, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [map_smul, map_smul, hc s hs]

lemma mapChains_boundary_simplex_of_image (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) (ht : s.image f ∈ L) :
    boundary L (mapChains K L f (simplex K s)) =
      mapChains K L f (boundary K (simplex K s)) := by
  rw [mapChains_simplex K L f hs, boundary_simplex K hs, map_sum]
  have h (a : V) : mapChains K L f (simplex K (s.erase a)) = mapSimplex L f (s.erase a) :=
    mapChains_simplex_subset K L f hs (Finset.erase_subset a s)
  simp_rw [h]
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hinj), boundary_simplex L ht]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      have hj : Set.InjOn f (s.erase a) := hinj.mono (Finset.erase_subset a s)
      rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hj), image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, ite_eq_right (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]

lemma mapChains_boundary_of_support (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∈ L) :
    boundary L (mapChains K L f c) = mapChains K L f (boundary K c) := by
  apply linearMap_eq_of_support ((boundary L).comp (mapChains K L f))
    ((mapChains K L f).comp (boundary K)) c
  intro s hs
  exact mapChains_boundary_simplex_of_image K L f s.property (hc s hs)

omit [DecidableEq V] in
lemma mapChains_augmentation_simplex_of_image (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) (ht : s.image f ∈ L) :
    augmentation L (mapChains K L f (simplex K s)) = augmentation K (simplex K s) := by
  rw [mapChains_simplex K L f hs, augmentation_simplex K hs]
  by_cases hcard : (s.image f).card = s.card
  · rw [mapSimplex, ite_eq_left hcard, augmentation_simplex L ht, hcard]
  · have hne : s.card ≠ 1 := by
      intro hc
      obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hc
      simp at hcard
    simp [mapSimplex, hcard, hne]

omit [DecidableEq V] in
lemma mapChains_augmentation_of_support (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∈ L) :
    augmentation L (mapChains K L f c) = augmentation K c := by
  apply linearMap_eq_of_support ((augmentation L).comp (mapChains K L f)) (augmentation K) c
  intro s hs
  exact mapChains_augmentation_simplex_of_image K L f s.property (hc s hs)

omit [DecidableEq V] in
lemma mapChains_degree_all (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (mapChains K L f) := by
  apply grade_map K L _ d d
  intro s hs hd
  rw [mapChains_simplex K L f hs, mapSimplex]
  split_ifs with hh
  · rw [← hd, ← hh]
    exact simplex_mem_degree_all L _
  · exact Submodule.zero_mem _

lemma mapChains_equivariant (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (f : V → W) (hf : ∀ s ∈ K, ∀ x ∈ s, f (e x) = d (f x)) :
    (mapChains L L d).comp (mapChains K L f) =
      (mapChains K L f).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have him : (s.val.image e).image f = (s.val.image f).image d := by
    simp only [Finset.image_image]
    exact Finset.image_congr (fun x hx => hf s.val s.property x hx)
  have hcard : (s.val.image e).card = s.val.card := Finset.card_image_iff.mpr e.injective.injOn
  have hcard' : ((s.val.image f).image d).card = (s.val.image f).card :=
    Finset.card_image_iff.mpr d.injective.injOn
  have hh : mapChains L L d (mapChains K L f (simplex K s.val)) =
      mapChains K L f (mapChains K K e (simplex K s.val)) := by
    rw [mapChains_simplex K L f s.property, mapChains_equiv_simplex_all K e he,
      mapChains_simplex K L f ((he s.val).mp s.property)]
    simp only [mapSimplex, him, hcard, hcard']
    split_ifs
    · exact mapChains_equiv_simplex_all L d hd _
    · exact map_zero _
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]

lemma mapChains_norm (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (f : V → W) (hf : ∀ s ∈ K, ∀ x ∈ s, f (e x) = d (f x)) :
    (normMap L d).comp (mapChains K L f) =
      (mapChains K L f).comp (normMap K e) := by
  simp only [normMap, LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
    LinearMap.comp_id, mapChains_equivariant K L e d he hd f hf]

end BorsukNine.SimplicialChains

end OAI
