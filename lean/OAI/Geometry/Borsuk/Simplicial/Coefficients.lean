import Mathlib
import OAI.Geometry.Borsuk.Simplicial.SignedVertex

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

section Coefficients
variable {V : Type*} [DecidableEq V] (K : PreAbstractSimplicialComplex V)

omit [DecidableEq V] in
lemma degreeChains_card_of_ne_zero (n : ℕ) {c : Chain K}
    (hc : c ∈ degreeChains K n) (s : {s : Finset V // s ∈ K}) (hs : c s ≠ 0) :
    s.val.card = n := by
  by_contra h
  exact hs ((Finsupp.mem_supported' F₂ c).mp hc s h)

lemma simplex_coeff (s : Finset V) (t : {t : Finset V // t ∈ K}) :
    simplex K s t = if s = t.val then 1 else 0 := by
  classical
  by_cases hs : s ∈ K
  · rw [simplex_of_mem K hs]
    simp only [Finsupp.single_apply]
    congr 1
    exact propext Subtype.ext_iff
  · have hst : s ≠ t.val := fun h => hs (h ▸ t.property)
    simp [simplex, hs, hst]

lemma boundary_simplex_coeff {s : Finset V} (hs : s ∈ K)
    (t : {t : Finset V // t ∈ K}) (hcard : t.val.card + 1 = s.card) :
    boundary K (simplex K s) t = if t.val ⊆ s then 1 else 0 := by
  classical
  rw [boundary_simplex K hs, Finsupp.finsetSum_apply]
  simp_rw [simplex_coeff]
  by_cases hts : t.val ⊆ s
  · rw [ite_eq_left hts]
    obtain ⟨a,ha,rfl⟩ := Finset.exists_eq_insert_iff.mpr ⟨hts,hcard⟩
    rw [Finset.sum_insert ha, Finset.erase_insert ha, ite_eq_left rfl]
    have hz : ∀ b ∈ t.val, (if (insert a t.val).erase b = t.val then (1:F₂) else 0) = 0 := by
      intro b hb
      rw [ite_eq_right]
      intro he
      have hab : a ≠ b := fun h => ha (h ▸ hb)
      have hh : a ∈ (insert a t.val).erase b := Finset.mem_erase.mpr
        ⟨hab, Finset.mem_insert_self _ _⟩
      exact ha (he ▸ hh)
    rw [Finset.sum_eq_zero hz, add_zero]
  · rw [ite_eq_right hts]
    apply Finset.sum_eq_zero
    intro a ha
    rw [ite_eq_right]
    intro he
    exact hts (he ▸ Finset.erase_subset a s)

end Coefficients

noncomputable def crossFacet (n : ℕ) (b : Fin n → Bool) : Finset SignedVertex :=
  Finset.univ.image (fun i : Fin n => (i.val,b i))

lemma mem_crossFacet (n : ℕ) (b : Fin n → Bool) (v : SignedVertex) :
    v ∈ crossFacet n b ↔ ∃ i : Fin n, v = (i.val,b i) := by
  classical
  simp only [crossFacet, Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_congr (fun _ => eq_comm)

lemma crossFacet_card (n : ℕ) (b : Fin n → Bool) : (crossFacet n b).card = n := by
  classical
  rw [crossFacet, Finset.card_image_iff.mpr, Finset.card_univ, Fintype.card_fin]
  intro i _ j _ hij
  exact Fin.ext (congrArg Prod.fst hij)

lemma crossFacet_mem (n : ℕ) (hn : 0 < n) (b : Fin n → Bool) : crossFacet n b ∈ cross n := by
  classical
  refine ⟨?_,?_,?_⟩
  · exact Finset.card_pos.mp (by rw [crossFacet_card]; exact hn)
  · intro v hv
    obtain ⟨i,rfl⟩ := (mem_crossFacet n b v).mp hv
    exact i.isLt
  · intro v hv w hw he
    obtain ⟨i,rfl⟩ := (mem_crossFacet n b v).mp hv
    obtain ⟨j,rfl⟩ := (mem_crossFacet n b w).mp hw
    have hij : i = j := Fin.ext he
    rw [hij]

lemma cross_top_exists_signs (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n)
    (hcard : s.card = n) : ∃ b : Fin n → Bool, s = crossFacet n b := by
  classical
  have hproj : s.image Prod.fst = Finset.range n := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (hs.2.1 v hv)
    · rw [Finset.card_image_iff.mpr hs.2.2, Finset.card_range, hcard]
  have hex (i : Fin n) : ∃ v ∈ s, v.1 = i.val := by
    apply Finset.mem_image.mp
    rw [hproj]
    exact Finset.mem_range.mpr i.isLt
  choose v hv hvi using hex
  refine ⟨fun i => (v i).2, ?_⟩
  ext w
  constructor
  · intro hw
    let i : Fin n := ⟨w.1,hs.2.1 w hw⟩
    have he : w = v i := hs.2.2 hw (hv i) (hvi i).symm
    apply (mem_crossFacet n _ w).mpr
    refine ⟨i, ?_⟩
    apply Prod.ext
    · rfl
    · change w.2 = (v i).2
      exact congrArg Prod.snd he
  · intro hw
    obtain ⟨i,rfl⟩ := (mem_crossFacet n _ w).mp hw
    have he : (i.val,(v i).2) = v i := Prod.ext (hvi i).symm rfl
    rw [he]
    exact hv i

end BorsukNine.SimplicialChains

end OAI
