import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.LookupExtraction

namespace OAI

noncomputable section

namespace Foulkes.Lookup
open MvPolynomial Finset Foulkes.Strips

lemma sorted_dominance {n : ℕ} (l w : Fin n → ℕ) (hl : Antitone l)
    (hw : ∀ j, w j ≤ l j) (j : Fin n) : w (sortDesc w j) ≤ l j := by
  classical
  by_contra h
  let e : Fin (j.val+1) → Fin n := fun c => ⟨c.val, by omega⟩
  have hrow (c : Fin (j.val+1)) : (sortDesc w (e c)).val < j.val := by
    by_contra hh
    have hw' : w (sortDesc w j) ≤ w (sortDesc w (e c)) :=
      sortDesc_antitone w (by change c.val ≤ j.val; omega)
    have hl' : l (sortDesc w (e c)) ≤ l j := hl (by change j.val ≤ _; omega)
    have hc := hw (sortDesc w (e c))
    omega
  let f : Fin (j.val+1) → Fin j.val := fun c => ⟨(sortDesc w (e c)).val, hrow c⟩
  have hf : Function.Injective f := by
    intro c d hcd
    have hv := congrArg (fun z : Fin j.val => z.val) hcd
    have hh : sortDesc w (e c) = sortDesc w (e d) := Fin.ext hv
    exact Fin.ext (congrArg (fun z : Fin n => z.val) ((sortDesc w).injective hh))
  have hn := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hn
  omega

theorem previous_partition_le {n : ℕ} (mu : Fin n → ℕ) (hm : Antitone mu)
    (i : ℕ) (d : Fin n →₀ ℕ)
    (_hn : ∀ j, 0 ≤ (shifted mu j : ℤ) - (i : ℤ)*d j) :
    ∀ j, sortedPartition (fun j => ((shifted mu j : ℤ) - (i : ℤ)*d j).toNat) j ≤ mu j := by
  intro j
  let w := fun j => ((shifted mu j : ℤ) - (i : ℤ)*d j).toNat
  have hw : ∀ j, w j ≤ shifted mu j := by
    intro j
    dsimp [w]
    exact Int.toNat_le.mpr (sub_le_self _ (by positivity))
  have hh := sorted_dominance (shifted mu) w (shifted_antitone hm) hw j
  change w (sortDesc w j) - staircase n j ≤ mu j
  change w (sortDesc w j) ≤ mu j + staircase n j at hh
  omega

lemma shifted_strictAnti {n : ℕ} {mu : Fin n → ℕ} (hm : Antitone mu) :
    StrictAnti (shifted mu) := by
  intro j k hjk
  have hh := hm (le_of_lt hjk)
  have hjn := j.isLt
  have hkn := k.isLt
  change mu k + (n-1-k.val) < mu j + (n-1-j.val)
  change j.val < k.val at hjk
  omega

lemma eq_of_strict_coefficients {n : ℕ} {p q : MvPolynomial (Fin n) ℤ}
    (hp : Alternating p) (hq : Alternating q)
    (h : ∀ v : Fin n → ℕ, StrictAnti v → p.coeff (expVector v) = q.coeff (expVector v)) : p = q := by
  classical
  ext d
  let v : Fin n → ℕ := fun j => d j
  have hd : expVector v = d := by ext j; rfl
  rw [← hd]
  by_cases hv : Function.Injective v
  · rw [coeff_eq_sign_mul_comp hp v (sortDesc v), coeff_eq_sign_mul_comp hq v (sortDesc v),
      h (v ∘ sortDesc v) (sortDesc_strict v hv)]
  · obtain ⟨j,k,hjk,he⟩ : ∃ j k, j ≠ k ∧ v j = v k := by
      simpa only [Function.Injective, not_forall, exists_prop, Classical.not_imp, ne_eq,
        and_comm] using hv
    rw [coeff_repeated hp v hjk he, coeff_repeated hq v hjk he]

lemma coeff_alternant_strict {n : ℕ} (m v : Fin n → ℕ)
    (hm : StrictAnti m) (hv : StrictAnti v) :
    (alternant m).coeff (expVector v) = if m = v then 1 else 0 := by
  classical
  have hper (σ : Equiv.Perm (Fin n)) :
      expVector (m ∘ σ.symm) = expVector v ↔ m = v ∧ σ = 1 := by
    constructor
    · intro he
      have he' : m ∘ σ.symm = v := Finsupp.equivFunOnFinite.symm.injective he
      have hs : m ∘ σ.symm = m := Tuple.unique_antitone
        (he'.symm ▸ hv.antitone) (show Antitone (m ∘ (1 : Equiv.Perm (Fin n))) from hm.antitone)
      have hid : σ.symm = 1 := by
        apply Equiv.ext
        intro j
        exact hm.injective (congrFun hs j)
      have hσ : σ = 1 := by
        change σ⁻¹ = 1 at hid
        exact inv_eq_one.mp hid
      exact ⟨hs.symm.trans he',hσ⟩
    · rintro ⟨rfl,rfl⟩; rfl
  have ha : alternant m = ∑ σ : Equiv.Perm (Fin n),
      Equiv.Perm.sign σ • ∏ c, (X (σ c) : MvPolynomial (Fin n) ℤ) ^ m c :=
    Matrix.det_apply _
  rw [ha, coeff_sum]
  simp_rw [coeff_smul, perm_prod_monomial]
  change (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ) •
    (monomial (expVector (m ∘ σ.symm)) (1 : ℤ)).coeff (expVector v)) = _
  simp_rw [coeff_monomial, hper]
  by_cases he : m = v
  · simp [he]
  · simp [he]

lemma alternating_sum {α : Type*} {n : ℕ} (s : Finset α)
    (p : α → MvPolynomial (Fin n) ℤ) (hp : ∀ a ∈ s, Alternating (p a)) :
    Alternating (∑ a ∈ s, p a) := by
  intro σ
  simp only [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun a ha => hp a ha σ)

lemma alternating_smul {n : ℕ} (z : ℤ) {p : MvPolynomial (Fin n) ℤ}
    (hp : Alternating p) : Alternating (z • p) := by
  intro σ
  rw [map_smul, hp σ, smul_comm]

theorem alternant_expansion {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (hp : Alternating p) :
    p = ∑ d ∈ p.support.filter (fun d => StrictAnti (fun j => d j)),
      p.coeff d • alternant (fun j => d j) := by
  classical
  let s := p.support.filter (fun d => StrictAnti (fun j => d j))
  apply eq_of_strict_coefficients hp
    (alternating_sum s _ (fun _ _ => alternating_smul _ (alternant_alternating _)))
  intro v hv
  rw [coeff_sum]
  have hd (d : Fin n →₀ ℕ) (hd : d ∈ s) :
      (p.coeff d • alternant (fun j => d j)).coeff (expVector v) =
        if d = expVector v then p.coeff d else 0 := by
    rw [coeff_smul, coeff_alternant_strict _ _ (mem_filter.mp hd).2 hv]
    have he : (fun j => d j) = v ↔ d = expVector v := by
      constructor
      · intro h; ext j; exact congrFun h j
      · intro h; subst d; rfl
    simp [he]
  change p.coeff (expVector v) = ∑ d ∈ s, _
  rw [Finset.sum_congr rfl hd]
  by_cases hmem : expVector v ∈ s
  · simp [hmem]
  · have hc : p.coeff (expVector v) = 0 := by
      have hh : expVector v ∉ p.support := fun hh => hmem (by exact mem_filter.mpr ⟨hh,hv⟩)
      exact notMem_support_iff.mp hh
    simp [hmem,hc]

end Foulkes.Lookup

end

end OAI
