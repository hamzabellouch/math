import Mathlib
import OAI.Geometry.Borsuk.Simplicial.CharacteristicDegree
import OAI.Geometry.Borsuk.Simplicial.Flip

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

lemma bool_cube_constant {n : ℕ} {A : Type*} (p : (Fin n → Bool) → A)
    (hp : ∀ b i, p b = p (flipAt b i)) (b c : Fin n → Bool) : p b = p c := by
  classical
  suffices hs : ∀ (s : Finset (Fin n)) (b c : Fin n → Bool),
      (∀ i ∉ s, b i = c i) → p b = p c by
    exact hs Finset.univ b c (by simp)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro b c h
    have he : b = c := funext (fun i => h i (by simp))
    rw [he]
  | @insert i s _ ih =>
    intro b c h
    let d := Function.update b i (c i)
    have hd : ∀ j ∉ s, d j = c j := by
      intro j hj
      by_cases he : j = i
      · subst j; simp [d]
      · simpa [d, he] using h j (by simp [hj, he])
    have he : p b = p d := by
      by_cases hb : b i = c i
      · have hbd : b = d := by
          funext j
          by_cases hji : j = i
          · subst j; simpa [d] using hb
          · simp [d, hji]
        rw [hbd]
      · have hflip : c i = !b i := by
          cases hbi : b i <;> cases hci : c i <;> simp_all
        have hdflip : d = flipAt b i := by simp only [d, flipAt, hflip]
        rw [hdflip]
        exact hp b i
    exact he.trans (ih d c hd)

lemma cross_cycle_coeff_constant (n : ℕ) (hn : 1 < n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n)
    (hd : boundary (cross n) c = 0) (b d : Fin n → Bool) :
    c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ =
      c ⟨crossFacet n d,crossFacet_mem n (by omega) d⟩ :=
  bool_cube_constant _ (fun b i => cross_cycle_adjacent_coeff n hn b i c hc hd) b d

lemma crossFundamental_coeff (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) :
    crossFundamental n ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ = 1 := by
  have hnonzero : crossFundamental n ≠ 0 := by
    intro h
    have hd := characteristicDegree_crossFundamental n (by omega)
    rw [h, map_zero] at hd
    exact zero_ne_one hd
  obtain ⟨s,hs⟩ : ∃ s, crossFundamental n s ≠ 0 := by
    by_contra h
    push Not at h
    exact hnonzero (Finsupp.ext h)
  have hcard : s.val.card = n := degreeChains_card_of_ne_zero (cross n) n
    (crossFundamental_degree n (by omega)) s hs
  obtain ⟨d,hd⟩ := cross_top_exists_signs n s.val s.property hcard
  have hsd : s = ⟨crossFacet n d,crossFacet_mem n (by omega) d⟩ := Subtype.ext hd
  rw [hsd] at hs
  have hconst := cross_cycle_coeff_constant n hn (crossFundamental n)
    (crossFundamental_degree n (by omega)) (crossFundamental_boundary n (by omega)) b d
  rw [hconst]
  have h₂ : ∀ x : F₂, x = 0 ∨ x = 1 := by decide
  exact (h₂ _).resolve_left hs

lemma cross_top_cycle_eq (n : ℕ) (hn : 1 < n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n)
    (hd : boundary (cross n) c = 0) (b : Fin n → Bool) :
    c = c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ • crossFundamental n := by
  classical
  ext s
  rw [Finsupp.smul_apply, smul_eq_mul]
  by_cases hcard : s.val.card = n
  · obtain ⟨d,hd'⟩ := cross_top_exists_signs n s.val s.property hcard
    have hsd : s = ⟨crossFacet n d,crossFacet_mem n (by omega) d⟩ := Subtype.ext hd'
    rw [hsd, crossFundamental_coeff n hn d, mul_one]
    exact cross_cycle_coeff_constant n hn c hc hd d b
  · have hz : c s = 0 := by
      by_contra hs
      exact hcard (degreeChains_card_of_ne_zero (cross n) n hc s hs)
    have hz' : crossFundamental n s = 0 := by
      by_contra hs
      exact hcard (degreeChains_card_of_ne_zero (cross n) n
        (crossFundamental_degree n (by omega)) s hs)
    rw [hz, hz', mul_zero]

lemma cross_characteristicDegree_eq_coeff (n : ℕ) (hn : 1 < n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n)
    (hd : boundary (cross n) c = 0) (b : Fin n → Bool) :
    characteristicDegree (cross n) flip (cross_flip n) flip_involutive (cross_free n)
      (n-1) c = c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ := by
  conv_lhs => rw [cross_top_cycle_eq n hn c hc hd b]
  rw [map_smul, characteristicDegree_crossFundamental n (by omega), smul_eq_mul, mul_one]

end BorsukNine.SimplicialChains

end OAI
