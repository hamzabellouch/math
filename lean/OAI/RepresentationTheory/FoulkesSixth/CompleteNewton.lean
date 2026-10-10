import Mathlib

namespace OAI

noncomputable section

namespace Foulkes.Complete
open MvPolynomial Finset

abbrev Degree (α : Type*) (b : ℕ) := {d : α →₀ ℕ // d.degree = b}
instance {α : Type*} [Finite α] (b : ℕ) : Fintype (Degree α b) :=
  (Finsupp.finite_of_degree_eq (σ := α) b).fintype

def h (α : Type*) [Finite α] (b : ℕ) : MvPolynomial α ℤ :=
  ∑ d : Degree α b, monomial d.val 1

@[simp] theorem coeff_h {α : Type*} [Finite α] (b : ℕ) (d : α →₀ ℕ) :
    (h α b).coeff d = if d.degree = b then 1 else 0 := by
  classical
  simp only [h, coeff_sum, coeff_monomial]
  by_cases hd : d.degree = b
  · rw [ite_eq_left hd, Finset.sum_eq_single (⟨d,hd⟩ : Degree α b)]
    · simp
    · intro e he hne
      have hneq : e.val ≠ d := fun hh => hne (Subtype.ext hh)
      simp [hneq]
    · simp
  · rw [ite_eq_right hd]
    apply Finset.sum_eq_zero
    intro e he
    have hneq : e.val ≠ d := fun hh => hd (hh ▸ e.property)
    simp [hneq]

@[simp] theorem h_zero (α : Type*) [Finite α] : h α 0 = 1 := by
  classical
  ext d
  rw [coeff_h]
  by_cases hd : d = 0
  · simp [hd]
  · have hh : d.degree ≠ 0 := by
      intro hh
      apply hd
      ext j
      have hj := Finsupp.le_degree j d
      simp only [hh, Nat.le_zero] at hj
      simpa using hj
    simp [hh, coeff_one, Ne.symm hd]

lemma coeff_X_pow_h {α : Type*} [Finite α] (b k : ℕ) (hkb : k ≤ b)
    (j : α) (d : α →₀ ℕ) :
    ((X j : MvPolynomial α ℤ)^k * h α (b-k)).coeff d =
      if d.degree = b ∧ k ≤ d j then 1 else 0 := by
  classical
  rw [X_pow_eq_monomial, coeff_monomial_mul', coeff_h]
  simp only [one_mul, Finsupp.single_le_iff]
  by_cases hk : k ≤ d j
  · rw [ite_eq_left hk]
    have hs : Finsupp.single j k ≤ d := Finsupp.single_le_iff.mpr hk
    have he : (d - Finsupp.single j k).degree + k = d.degree := by
      have he := congrArg Finsupp.degree (tsub_add_cancel_of_le hs)
      simpa using he
    have hd : (d - Finsupp.single j k).degree = b-k ↔ d.degree = b := by omega
    simp only [hd, hk, and_true]
  · simp [hk]

theorem newton {α : Type*} [Fintype α] (b : ℕ) :
    (b : ℤ) • h α b =
      ∑ k ∈ Finset.Icc 1 b, (∑ j : α, (X j : MvPolynomial α ℤ)^k) * h α (b-k) := by
  classical
  ext d
  simp only [coeff_smul, coeff_h, coeff_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  by_cases hd : d.degree = b
  · have hterm (j : α) :
        ∑ k ∈ Finset.Icc 1 b, ((X j : MvPolynomial α ℤ)^k * h α (b-k)).coeff d = (d j : ℤ) := by
      have hj : d j ≤ b := by simpa [hd] using Finsupp.le_degree j d
      have he : (Finset.Icc 1 b).filter (fun k => k ≤ d j) = Finset.Icc 1 (d j) := by
        ext k
        simp only [mem_filter, mem_Icc]
        omega
      calc
        _ = ∑ k ∈ Finset.Icc 1 b, if k ≤ d j then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [coeff_X_pow_h b k (mem_Icc.mp hk).2]
          simp only [hd, true_and]
        _ = ((Finset.Icc 1 (d j)).card : ℤ) := by
          rw [← Finset.sum_filter, he]
          simp
        _ = (d j : ℤ) := by simp
    simp only [hterm, ite_eq_left hd, zsmul_eq_mul, mul_one]
    simpa using
      congrArg (fun z : ℕ => (z : ℤ)) (hd.symm.trans (Finsupp.degree_eq_sum d))
  · have hterm (j : α) :
        ∑ k ∈ Finset.Icc 1 b, ((X j : MvPolynomial α ℤ)^k * h α (b-k)).coeff d = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [coeff_X_pow_h b k (mem_Icc.mp hk).2]
      simp [hd]
    simp [hterm, hd]

def alphabetH {α σ : Type*} [Finite α] (x : α → MvPolynomial σ ℤ) (b : ℕ) : MvPolynomial σ ℤ :=
  eval₂Hom (Int.castRingHom _) x (h α b)

@[simp] theorem alphabetH_zero {α σ : Type*} [Finite α] (x : α → MvPolynomial σ ℤ) :
    alphabetH x 0 = 1 := by simp [alphabetH]

theorem alphabet_newton {α σ : Type*} [Fintype α] (x : α → MvPolynomial σ ℤ) (b : ℕ) :
    (b : ℤ) • alphabetH x b =
      ∑ k ∈ Finset.Icc 1 b, (∑ j : α, x j ^ k) * alphabetH x (b-k) := by
  have hh := congrArg (eval₂Hom (Int.castRingHom (MvPolynomial σ ℤ)) x) (newton (α := α) b)
  simpa [alphabetH] using hh

def pleth (n b a : ℕ) : MvPolynomial (Fin n) ℤ :=
  alphabetH (fun d : Degree (Fin n) a => monomial d.val 1) b

@[simp] theorem pleth_zero (n a : ℕ) : pleth n 0 a = 1 := alphabetH_zero _

theorem pleth_newton (n b a : ℕ) :
    (b : ℤ) • pleth n b a =
      ∑ k ∈ Finset.Icc 1 b,
        (∑ d : Degree (Fin n) a, monomial (k • d.val) (1 : ℤ)) * pleth n (b-k) a := by
  simpa [pleth, monomial_pow] using
    (alphabet_newton (fun d : Degree (Fin n) a => monomial d.val (1 : ℤ)) b)

end Foulkes.Complete

end

end OAI
