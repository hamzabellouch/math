import Mathlib
import OAI.Geometry.Borsuk.Simplicial.LinearMapSupport
import OAI.Geometry.Borsuk.Simplicial.Coefficients

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

noncomputable def flipAt {n : ℕ} (b : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update b i (! b i)

lemma flipAt_ne {n : ℕ} (b : Fin n → Bool) (i : Fin n) : flipAt b i ≠ b := by
  intro he
  have hi := congrFun he i
  simp [flipAt] at hi

lemma crossFacet_injective (n : ℕ) : Function.Injective (crossFacet n) := by
  intro b c he
  funext i
  have hi : (i.val,b i) ∈ crossFacet n c := he ▸ (mem_crossFacet n b _).mpr ⟨i,rfl⟩
  obtain ⟨j,hj⟩ := (mem_crossFacet n c _).mp hi
  have hij : i = j := Fin.ext (congrArg Prod.fst hj)
  simpa only [← hij] using congrArg Prod.snd hj

noncomputable def crossRidge (n : ℕ) (b : Fin n → Bool) (i : Fin n) : Finset SignedVertex :=
  (crossFacet n b).erase (i.val,b i)

lemma crossRidge_card (n : ℕ) (b : Fin n → Bool) (i : Fin n) :
    (crossRidge n b i).card = n-1 := by
  rw [crossRidge, Finset.card_erase_of_mem ((mem_crossFacet n b _).mpr ⟨i,rfl⟩),
    crossFacet_card]

lemma crossRidge_mem (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) (i : Fin n) :
    crossRidge n b i ∈ cross n := by
  apply ((cross n).isRelLowerSet_faces (crossFacet_mem n (by omega) b)).2
    (Finset.erase_subset _ _)
  apply Finset.card_pos.mp
  change 0 < (crossRidge n b i).card
  rw [crossRidge_card]
  omega

lemma mem_crossRidge (n : ℕ) (b : Fin n → Bool) (i : Fin n) (v : SignedVertex) :
    v ∈ crossRidge n b i ↔ ∃ j : Fin n, j ≠ i ∧ v = (j.val,b j) := by
  classical
  simp only [crossRidge, Finset.mem_erase, mem_crossFacet]
  constructor
  · rintro ⟨hne,j,rfl⟩
    exact ⟨j, fun h => hne (h ▸ rfl), rfl⟩
  · rintro ⟨j,hji,rfl⟩
    refine ⟨?_,j,rfl⟩
    exact fun h => hji (Fin.ext (congrArg Prod.fst h))

lemma crossRidge_subset_iff (n : ℕ) (b c : Fin n → Bool) (i : Fin n) :
    crossRidge n b i ⊆ crossFacet n c ↔ ∀ j : Fin n, j ≠ i → c j = b j := by
  constructor
  · intro h j hji
    have hj := h ((mem_crossRidge n b i _).mpr ⟨j,hji,rfl⟩)
    obtain ⟨k,hk⟩ := (mem_crossFacet n c _).mp hj
    have hjk : j = k := Fin.ext (congrArg Prod.fst hk)
    simpa only [← hjk] using (congrArg Prod.snd hk).symm
  · intro h v hv
    obtain ⟨j,hji,rfl⟩ := (mem_crossRidge n b i v).mp hv
    exact (mem_crossFacet n c _).mpr ⟨j, by rw [h j hji]⟩

lemma crossRidge_parents (n : ℕ) (b c : Fin n → Bool) (i : Fin n) :
    crossRidge n b i ⊆ crossFacet n c ↔ c = b ∨ c = flipAt b i := by
  rw [crossRidge_subset_iff]
  constructor
  · intro h
    by_cases hi : c i = b i
    · left
      funext j
      by_cases hj : j = i
      · subst j; exact hi
      · exact h j hj
    · right
      have hb : c i = !b i := by cases hci : c i <;> cases hbi : b i <;> simp_all
      funext j
      by_cases hj : j = i
      · subst j; simpa [flipAt] using hb
      · simpa [flipAt, hj] using h j hj
  · rintro (rfl | rfl) j hj
    · rfl
    · simp [flipAt, hj]

lemma boundary_ridge_coefficient (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) (i : Fin n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n) :
    boundary (cross n) c ⟨crossRidge n b i,crossRidge_mem n hn b i⟩ =
      c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ +
      c ⟨crossFacet n (flipAt b i),crossFacet_mem n (by omega) (flipAt b i)⟩ := by
  classical
  let r : {s : Finset SignedVertex // s ∈ cross n} :=
    ⟨crossRidge n b i,crossRidge_mem n hn b i⟩
  let s : {s : Finset SignedVertex // s ∈ cross n} :=
    ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩
  let t : {s : Finset SignedVertex // s ∈ cross n} :=
    ⟨crossFacet n (flipAt b i),crossFacet_mem n (by omega) (flipAt b i)⟩
  let α : Chain (cross n) →ₗ[F₂] F₂ := Finsupp.lapply s + Finsupp.lapply t
  change ((Finsupp.lapply r).comp (boundary (cross n))) c = α c
  apply linearMap_eq_of_support
  intro a ha
  have hcard : a.val.card = n := degreeChains_card_of_ne_zero (cross n) n hc a (Finsupp.mem_support_iff.mp ha)
  obtain ⟨d,hd⟩ := cross_top_exists_signs n a.val a.property hcard
  have hcoeff := boundary_simplex_coeff (cross n) a.property r (by
    change (crossRidge n b i).card + 1 = a.val.card
    rw [crossRidge_card, hcard]
    omega)
  simp only [α, LinearMap.comp_apply, Finsupp.lapply_apply, LinearMap.add_apply]
  rw [hcoeff, simplex_coeff, simplex_coeff]
  change (if crossRidge n b i ⊆ a.val then (1:F₂) else 0) =
    (if a.val = crossFacet n b then 1 else 0) +
    (if a.val = crossFacet n (flipAt b i) then 1 else 0)
  rw [hd]
  simp only [crossRidge_parents, crossFacet_injective n |>.eq_iff]
  have hne : flipAt b i ≠ b := flipAt_ne b i
  by_cases hb : d = b <;> by_cases ht : d = flipAt b i <;> simp_all

lemma cross_cycle_adjacent_coeff (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) (i : Fin n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n) (hd : boundary (cross n) c = 0) :
    c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ =
      c ⟨crossFacet n (flipAt b i),crossFacet_mem n (by omega) (flipAt b i)⟩ := by
  have h := boundary_ridge_coefficient n hn b i c hc
  rw [hd, Finsupp.zero_apply] at h
  have he := eq_neg_of_add_eq_zero_left h.symm
  simpa only [CharTwo.neg_eq] using he

end BorsukNine.SimplicialChains

end OAI
