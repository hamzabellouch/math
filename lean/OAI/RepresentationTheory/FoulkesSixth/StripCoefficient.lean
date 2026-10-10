import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.StripSupport

namespace OAI

noncomputable section

namespace Foulkes.Strips
open MvPolynomial Finset Matrix

def Composition (n b : ℕ) := {v : Fin n → Fin (b+1) // ∑ j, (v j).val = b}
instance (n b : ℕ) : Fintype (Composition n b) :=
  inferInstanceAs (Fintype {_composition : Fin n → Fin (b+1) // _})

def completePowers (n i b : ℕ) : MvPolynomial (Fin n) ℤ :=
  ∑ v : Composition n b,
    monomial (Finsupp.equivFunOnFinite.symm (fun j => i*(v.val j).val)) 1

def alternant {n : ℕ} (m : Fin n → ℕ) : MvPolynomial (Fin n) ℤ :=
  Matrix.det fun r c => (X r : MvPolynomial (Fin n) ℤ) ^ m c

abbrev expVector {n : ℕ} (v : Fin n → ℕ) : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm v

@[simp] lemma expVector_apply {n : ℕ} (v : Fin n → ℕ) (j : Fin n) : expVector v j = v j := by
  simp [expVector]

lemma exponent_injective {n b i : ℕ} (hi : 0 < i) (d : Fin n → ℕ) :
    Function.Injective (fun v : Composition n b => expVector (fun j => i*(v.val j).val) + expVector d) := by
  intro v w h
  apply Subtype.ext
  funext j
  apply Fin.ext
  have hj := DFunLike.congr_fun h j
  simp only [Finsupp.add_apply, expVector_apply] at hj
  exact Nat.eq_of_mul_eq_mul_left hi (Nat.add_right_cancel hj)

lemma coeff_complete_monomial {n b i : ℕ} (hi : 0 < i) (l d : Fin n → ℕ) :
    (completePowers n i b * monomial (expVector d) 1).coeff (expVector l) =
      if ∃ v : Composition n b, expVector (fun j => i*(v.val j).val) + expVector d = expVector l
      then 1 else 0 := by
  classical
  simp only [completePowers, Finset.sum_mul, coeff_sum, monomial_mul_monomial, one_mul, coeff_monomial]
  split_ifs with h
  · obtain ⟨v,hv⟩ := h
    rw [Finset.sum_eq_single v]
    · simp [hv]
    · intro w hw hne
      have hh : expVector (fun j => i*(w.val j).val) + expVector d ≠ expVector l := by
        intro hw
        exact hne (exponent_injective hi d (hw.trans hv.symm))
      simp [hh]
    · simp
  · apply Finset.sum_eq_zero
    intro v hv
    simp only [ite_eq_right (fun hh => h ⟨v,hh⟩)]

lemma perm_prod_monomial {n : ℕ} (m : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    (∏ c, (X (σ c) : MvPolynomial (Fin n) ℤ) ^ m c) =
      monomial (expVector (fun r => m (σ.symm r))) 1 := by
  rw [monic_monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simpa using Equiv.prod_comp σ (fun r => (X r : MvPolynomial (Fin n) ℤ) ^ m (σ.symm r))

lemma exists_composition_iff {n b i : ℕ} (hi : 0 < i) (l d : Fin n → ℕ)
    (htotal : ∑ r, l r = (∑ r, d r) + i*b) :
    (∃ v : Composition n b, expVector (fun j => i*(v.val j).val) + expVector d = expVector l) ↔
      ∀ r, d r ≤ l r ∧ d r % i = l r % i := by
  classical
  constructor
  · rintro ⟨v,hv⟩ r
    have hr := DFunLike.congr_fun hv r
    simp only [Finsupp.add_apply, expVector_apply] at hr
    refine ⟨by omega, ?_⟩
    rw [← hr]
    simp
  · intro h
    let q : Fin n → ℕ := fun r => (l r - d r) / i
    have hq (r : Fin n) : i*q r + d r = l r := by
      have hdvd : i ∣ l r-d r := (Nat.modEq_iff_dvd' (h r).1).mp (h r).2
      dsimp [q]
      rw [Nat.mul_div_cancel' hdvd, Nat.sub_add_cancel (h r).1]
    have hsum : ∑ r, q r = b := by
      have hs : i*(∑ r, q r) + ∑ r, d r = ∑ r, l r := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun r hr => hq r)
      have he : i*(∑ r, q r) = i*b := by omega
      exact Nat.eq_of_mul_eq_mul_left hi he
    have hb (r : Fin n) : q r < b+1 := by
      have hh : q r ≤ ∑ j, q j := Finset.single_le_sum (fun j hj => Nat.zero_le _) (mem_univ r)
      omega
    let v : Composition n b := ⟨fun r => ⟨q r, hb r⟩, hsum⟩
    refine ⟨v, ?_⟩
    ext r
    exact hq r

lemma assignment_product {n : ℕ} (i : ℕ) (l m : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    (∏ c, incidence (assignments i l m) (σ c) c) =
      if ∀ r, m (σ.symm r) ≤ l r ∧ m (σ.symm r) % i = l r % i then 1 else 0 := by
  classical
  by_cases h : ∀ r, m (σ.symm r) ≤ l r ∧ m (σ.symm r) % i = l r % i
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro c hc
    have hh := h (σ c)
    simp only [incidence, assignments, mem_filter, mem_univ, true_and]
    rw [ite_eq_left (by simpa using hh)]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨r,hr⟩ := h
    apply Finset.prod_eq_zero (mem_univ (σ.symm r))
    simp only [incidence, assignments, mem_filter, mem_univ, true_and, Equiv.apply_symm_apply]
    exact ite_eq_right (fun hh => hr hh.1 hh.2)

theorem coefficient_eq_assignment_det {n b i : ℕ} (hi : 0 < i) (l m : Fin n → ℕ)
    (htotal : ∑ r, l r = (∑ r, m r) + i*b) :
    (completePowers n i b * alternant m).coeff (expVector l) =
      (incidence (assignments i l m)).det := by
  classical
  have ha : alternant m = ∑ σ : Equiv.Perm (Fin n),
      Equiv.Perm.sign σ • ∏ c, (X (σ c) : MvPolynomial (Fin n) ℤ) ^ m c :=
    Matrix.det_apply _
  rw [ha, Matrix.det_apply, Finset.mul_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [mul_smul_comm, coeff_smul, perm_prod_monomial, coeff_complete_monomial hi,
    assignment_product]
  have ht : ∑ r, l r = (∑ r, m (σ.symm r)) + i*b := by
    rw [Equiv.sum_comp σ.symm m]
    exact htotal
  simp only [exists_composition_iff hi l _ ht]

theorem signed_strip_abs_le_one {n b i : ℕ} (hi : 0 < i) (l m : Fin n → ℕ)
    (htotal : ∑ r, l r = (∑ r, m r) + i*b) :
    Int.natAbs ((completePowers n i b * alternant m).coeff (expVector l)) ≤ 1 := by
  rw [coefficient_eq_assignment_det hi l m htotal]
  exact assignment_det_bound i l m

end Foulkes.Strips

end

end OAI
