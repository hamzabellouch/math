import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.BooleanCoordinateGeneration
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ConditionalBooleanGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiveTrackGeneration

noncomputable def fiveTrackHom {m : ℕ} (ι : Fin 5 ↪ Fin m) :
    alternatingGroup (Fin 5) →* Equiv.Perm (Fin m) :=
  (Equiv.Perm.viaEmbeddingHom ι).comp (alternatingGroup (Fin 5)).subtype

instance fiveTrackPerfect : Group.IsPerfect (alternatingGroup (Fin 5)) :=
  ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩

theorem fiveTrack_sign {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (g : alternatingGroup (Fin 5)) : fiveTrackHom ι g ∈ alternatingGroup (Fin m) := by
  classical
  change Equiv.Perm.sign (g.val.viaEmbedding ι) = 1
  rw [Equiv.Perm.viaEmbedding,Equiv.Perm.sign_extendDomain]
  exact g.property

theorem fiveTrack_support {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (g : alternatingGroup (Fin 5)) : (fiveTrackHom ι g).support.card ≤ 5 := by
  classical
  have hsub : (fiveTrackHom ι g).support ⊆ Finset.univ.map ι := by
    intro i hi
    by_contra hn
    have hn' : i ∉ Set.range ι := by simpa using hn
    exact (Equiv.Perm.mem_support.mp hi) (Equiv.Perm.viaEmbedding_apply_of_notMem g.val ι i hn')
  simpa using Finset.card_le_card hsub

theorem fiveTrack_initial_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) (j : Fin 5) :
    ConditionalAvailable (fiveTrackHom ι) (sourceGenerated a r m) (initialTest a r j) := by
  intro g
  exact sourceGenerator_mem_generated a r m
    (Sum.inl (j,⟨fiveTrackHom ι g,fiveTrack_sign ι g,fiveTrack_support ι g⟩))

theorem fiveTrack_whole_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) :
    ConditionalAvailable (fiveTrackHom ι) (sourceGenerated a r m) (wholePolygon a) :=
  fiveTrack_initial_generated a r m ι 0

noncomputable def alphabetTranslation {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (b : Fin m) (u : CutRing × CutRing) : Fin m → CutRing × CutRing :=
  ∑ j : Fin 5, (Pi.single (ι j) u - Pi.single b u)

theorem alphabetTranslation_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (u : CutRing × CutRing) :
    trackTranslation (a := a) (alphabetTranslation ι b u) ∈ sourceGenerated a r m := by
  classical
  unfold alphabetTranslation
  induction (Finset.univ : Finset (Fin 5)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,trackTranslation_add]
    exact (sourceGenerated a r m).mul_mem (balanced_difference_generated a r m b (ι i) u) ih

theorem alphabetTranslation_apply {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (b : Fin m) (hb : b ∉ Set.range ι) (u : CutRing × CutRing) (j : Fin 5) :
    alphabetTranslation ι b u (ι j) = u := by
  classical
  have hb' : ∀ k, ι k ≠ b := fun k h => hb ⟨k,h⟩
  simp [alphabetTranslation,Finset.sum_apply,Pi.single_apply,ι.injective.eq_iff,hb']

theorem conditional_translation_conjugate {a m : ℕ} (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) (d : Fin m → CutRing × CutRing) (u : CutRing × CutRing)
    (hd : ∀ i, σ i ≠ i → d i = u) :
    conditionalHom (⟨translate a (-u) ⁻¹' U.val,
      polygon_preimage_translate (-u) U.property⟩ : polygonAlgebra a) σ =
      trackTranslation d * conditionalHom U σ * (trackTranslation d)⁻¹ := by
  classical
  apply Subtype.ext
  apply Equiv.ext
  rintro ⟨i,p⟩
  change conditionalPerm (⟨_,_⟩ : polygonAlgebra a) σ (i,p) =
    trackTranslationPerm d (conditionalPerm U σ ((trackTranslationPerm d).symm (i,p)))
  by_cases hi : σ i = i
  · simp [conditionalPerm,trackTranslationPerm,hi,← translate_add]
  · have hi' : σ (σ i) ≠ σ i := fun h => hi (σ.injective h)
    have hdi := hd i hi
    have hdsi := hd (σ i) hi'
    by_cases hp : translate a (-u) p ∈ U.val <;>
      simp_all [conditionalPerm,trackTranslationPerm,← translate_add]

theorem fiveTrack_translate_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (hb : b ∉ Set.range ι)
    (U : polygonAlgebra a)
    (hU : ConditionalAvailable (fiveTrackHom ι) (sourceGenerated a r m) U)
    (u : CutRing × CutRing) :
    ConditionalAvailable (fiveTrackHom ι) (sourceGenerated a r m)
      ⟨translate a u ⁻¹' U.val,polygon_preimage_translate u U.property⟩ := by
  intro g
  let d := alphabetTranslation ι b (-u)
  have hd : ∀ i, fiveTrackHom ι g i ≠ i → d i = -u := by
    intro i hi
    have hi' : i ∈ Set.range ι := by
      by_contra hn
      exact hi (Equiv.Perm.viaEmbedding_apply_of_notMem g.val ι i hn)
    obtain ⟨j,rfl⟩ := hi'
    exact alphabetTranslation_apply ι b hb (-u) j
  have he := conditional_translation_conjugate U (fiveTrackHom ι g) d (-u) hd
  simp only [neg_neg] at he
  rw [he]
  have ht := alphabetTranslation_generated a r m ι b (-u)
  exact (sourceGenerated a r m).mul_mem ((sourceGenerated a r m).mul_mem ht (hU g))
    ((sourceGenerated a r m).inv_mem ht)

noncomputable def fiveTrackBoolean (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) : BooleanSubalgebra (Set (GenericSquare a)) :=
  conditionalBoolean (fiveTrackHom ι) (sourceGenerated a r m)
    (fiveTrack_whole_generated a r m ι)

theorem fiveTrackBoolean_translate (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (hb : b ∉ Set.range ι)
    (u : CutRing × CutRing) {U : Set (GenericSquare a)}
    (hU : U ∈ fiveTrackBoolean a r m ι) :
    translate a u ⁻¹' U ∈ fiveTrackBoolean a r m ι := by
  obtain ⟨hU,hU'⟩ := hU
  exact ⟨polygon_preimage_translate u hU,
    fiveTrack_translate_generated a r m ι b hb ⟨U,hU⟩ hU' u⟩

theorem fiveTrackBoolean_initial (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) (j : Fin 5) :
    (initialTest a r j).val ∈ fiveTrackBoolean a r m ι :=
  ⟨(initialTest a r j).property,fiveTrack_initial_generated a r m ι j⟩

theorem fiveTrackBoolean_coordinate (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (hb : b ∉ Set.range ι)
    (j : Fin 2) (z : CutRing) :
    halfPlane a (Fin.castLE (by omega) j) z ∈ fiveTrackBoolean a r m ι := by
  apply coordinate_cuts_generated _ j
    (fun u _ hU => fiveTrackBoolean_translate a r m ι b hb u hU)
  fin_cases j
  · exact fiveTrackBoolean_initial a r m ι 1
  · exact fiveTrackBoolean_initial a r m ι 2

end FiveTrackGeneration

end SimpleAmenable
end
end

end OAI
