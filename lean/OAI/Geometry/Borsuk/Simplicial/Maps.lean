import Mathlib
import OAI.Geometry.Borsuk.Simplicial.F2

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V : Type*} [DecidableEq V]
section Maps
variable {W : Type*} [DecidableEq W]

noncomputable def mapSimplex (L : PreAbstractSimplicialComplex W) (f : V → W)
    (s : Finset V) : Chain L :=
  if (s.image f).card = s.card then simplex L (s.image f) else 0

omit [DecidableEq V] in
@[simp] lemma mapSimplex_empty (L : PreAbstractSimplicialComplex W) (f : V → W) :
    mapSimplex L f ∅ = 0 := by simp [mapSimplex]

noncomputable def mapChains (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) : Chain K →ₗ[F₂] Chain L :=
  Finsupp.linearCombination F₂ (fun s => mapSimplex L f s.val)

omit [DecidableEq V] in
lemma mapChains_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) : mapChains K L f (simplex K s) = mapSimplex L f s := by
  simp [simplex_of_mem K hs, mapChains, Finsupp.linearCombination_single]

omit [DecidableEq V] in
lemma mapChains_simplex_subset (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s t : Finset V} (ht : t ∈ K) (hs : s ⊆ t) :
    mapChains K L f (simplex K s) = mapSimplex L f s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact mapChains_simplex K L f ((K.isRelLowerSet_faces ht).2 hs hn)

lemma image_erase_of_injOn (f : V → W) (s : Finset V) (h : Set.InjOn f s)
    {a : V} (ha : a ∈ s) : (s.erase a).image f = (s.image f).erase (f a) := by
  ext b
  constructor
  · intro hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      exact (Finset.mem_erase.mp hx).1 (h (Finset.mem_of_mem_erase hx) ha he)
    · exact Finset.mem_image_of_mem f (Finset.mem_of_mem_erase hx)
  · intro hb
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨fun he => hne (congrArg f he), hx⟩, rfl⟩

lemma image_erase_collision (f : V → W) (s : Finset V) {a b : V}
    (hb : b ∈ s) (hne : a ≠ b) (he : f a = f b) : (s.erase a).image f = s.image f := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image_of_mem f (Finset.mem_of_mem_erase hx)
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    by_cases ha : x = a
    · subst x
      exact Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨Ne.symm hne, hb⟩, he.symm⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨ha, hx⟩, rfl⟩

lemma mapSimplex_boundary_degenerate (L : PreAbstractSimplicialComplex W)
    (f : V → W) (s : Finset V) (h : ¬ Set.InjOn f s) :
    (∑ a ∈ s, mapSimplex L f (s.erase a)) = 0 := by
  classical
  change ¬ ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b at h
  push Not at h
  obtain ⟨a, ha, b, hb, he, hne⟩ := h
  rw [Finset.sum_eq_add a b hne]
  · have hima := image_erase_collision f s hb hne he
    have himb := image_erase_collision f s ha hne.symm he.symm
    have hc : mapSimplex L f (s.erase a) = mapSimplex L f (s.erase b) := by
      simp only [mapSimplex, hima, himb, Finset.card_erase_of_mem ha, Finset.card_erase_of_mem hb]
    rw [hc]
    exact chain_add_self L _
  · intro c hc hca
    have hn : ¬ Set.InjOn f (s.erase c) := by
      intro hinj
      exact hne (hinj (Finset.mem_erase.mpr ⟨Ne.symm hca.1, ha⟩)
        (Finset.mem_erase.mpr ⟨Ne.symm hca.2, hb⟩) he)
    simp only [mapSimplex, Finset.card_image_iff, ite_eq_right hn]
  · exact fun hn => (hn ha).elim
  · exact fun hn => (hn hb).elim

lemma mapChains_boundary_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) {s : Finset V} (hs : s ∈ K) :
    boundary L (mapChains K L f (simplex K s)) =
      mapChains K L f (boundary K (simplex K s)) := by
  rw [mapChains_simplex K L f hs, boundary_simplex K hs, map_sum]
  have h (a : V) : mapChains K L f (simplex K (s.erase a)) = mapSimplex L f (s.erase a) :=
    mapChains_simplex_subset K L f hs (Finset.erase_subset a s)
  simp_rw [h]
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hinj), boundary_simplex L (hf s hs)]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      have hj : Set.InjOn f (s.erase a) := hinj.mono (Finset.erase_subset a s)
      rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hj), image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, ite_eq_right (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]

lemma mapChains_boundary (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) :
    (boundary L).comp (mapChains K L f) = (mapChains K L f).comp (boundary K) := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := mapChains_boundary_simplex K L f hf s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs]

omit [DecidableEq V] in
lemma mapChains_augmentation_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) {s : Finset V} (hs : s ∈ K) :
    augmentation L (mapChains K L f (simplex K s)) = augmentation K (simplex K s) := by
  rw [mapChains_simplex K L f hs, augmentation_simplex K hs]
  by_cases hcard : (s.image f).card = s.card
  · rw [mapSimplex, ite_eq_left hcard, augmentation_simplex L (hf s hs), hcard]
  · have hne : s.card ≠ 1 := by
      intro hc
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
      simp at hcard
    simp [mapSimplex, hcard, hne]

omit [DecidableEq V] in
lemma mapChains_augmentation (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) :
    (augmentation L).comp (mapChains K L f) = augmentation K := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := mapChains_augmentation_simplex K L f hf s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs]

end Maps

end BorsukNine.SimplicialChains

end OAI
