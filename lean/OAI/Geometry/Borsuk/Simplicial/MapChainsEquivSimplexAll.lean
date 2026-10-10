import Mathlib
import OAI.Geometry.Borsuk.Simplicial.SimplexMemDegreeAll

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W U : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq U]

omit [DecidableEq W] [DecidableEq U] in
lemma mapChains_equiv_simplex_all (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (s : Finset V) :
    mapChains K K e (simplex K s) = simplex K (s.image e) := by
  classical
  by_cases hs : s ∈ K
  · rw [mapChains_simplex K K e hs, mapSimplex,
      ite_eq_left (Finset.card_image_iff.mpr e.injective.injOn)]
  · have ht : s.image e ∉ K := (he s).not.mp hs
    simp [simplex, hs, ht]

omit [DecidableEq W] [DecidableEq U] in
lemma cone_equivariant (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (a : V) :
    (mapChains K K e).comp (cone K a) = (cone K (e a)).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have hm := mapChains_equiv_simplex_all K e he s.val
  have hc := cone_simplex K a s.property
  have hsc := cone_simplex K (e a) ((he s.val).mp s.property)
  have hh : mapChains K K e (cone K a (simplex K s.val)) =
      cone K (e a) (mapChains K K e (simplex K s.val)) := by
    rw [hc, hm, hsc]
    by_cases ha : a ∈ s.val
    · rw [ite_eq_left ha, ite_eq_left (Finset.mem_image_of_mem e ha), map_zero]
    · have hna : e a ∉ s.val.image e := by
        intro h
        obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp h
        exact ha (e.injective heq ▸ hb)
      rw [ite_eq_right ha, ite_eq_right hna, mapChains_equiv_simplex_all K e he,
        Finset.image_insert]
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]

omit [DecidableEq U] in
lemma subdivSimplex_equivariant (L : PreAbstractSimplicialComplex W)
    (e : V ≃ V) (d : W ≃ W) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) (s : Finset V) :
    mapChains L L d (subdivSimplex L b s) = subdivSimplex L b (s.image e) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp
    have hc : (s.image e).card = s.card := Finset.card_image_iff.mpr e.injective.injOn
    by_cases hs : s.card = 1
    · rw [subdivSimplex_one L b hs, subdivSimplex_one L b (hc.trans hs),
        mapChains_equiv_simplex_all L d hd, Finset.image_singleton, hb]
    · rw [subdivSimplex_many L b hn hs,
        subdivSimplex_many L b (hn.image e) (by omega)]
      have hcone := LinearMap.congr_fun (cone_equivariant L d hd (b s))
        (∑ a ∈ s, subdivSimplex L b (s.erase a))
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcone
      rw [hcone, map_sum, hb, Finset.sum_image (fun a _ b _ he => e.injective he)]
      apply congrArg (cone L (d (b s)))
      apply Finset.sum_congr rfl
      intro a ha
      rw [ih (s.erase a) (Finset.erase_ssubset ha), image_erase_of_injOn e s e.injective.injOn ha]

omit [DecidableEq U] in
lemma subdivMap_equivariant (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) :
    (mapChains L L d).comp (subdivMap K L b) =
      (subdivMap K L b).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have hh : mapChains L L d (subdivMap K L b (simplex K s.val)) =
      subdivMap K L b (mapChains K K e (simplex K s.val)) := by
    rw [subdivMap_simplex K L b s.property, subdivSimplex_equivariant L e d hd b hb,
      mapChains_equiv_simplex_all K e he, subdivMap_simplex K L b ((he s.val).mp s.property)]
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]

omit [DecidableEq U] in
lemma subdivMap_norm (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) :
    (normMap L d).comp (subdivMap K L b) =
      (subdivMap K L b).comp (normMap K e) := by
  simp only [normMap, LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
    LinearMap.comp_id, subdivMap_equivariant K L e d he hd b hb]

omit [DecidableEq U] in
lemma subdivMap_degree (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (subdivMap K L b) := by
  apply grade_map K L _ d d
  intro s hs hsd
  rw [subdivMap_simplex K L b hs, ← hsd]
  exact subdivSimplex_degree L b s

end BorsukNine.SimplicialChains

end OAI
