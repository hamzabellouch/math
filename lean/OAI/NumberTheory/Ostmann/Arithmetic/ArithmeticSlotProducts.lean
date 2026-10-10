import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticHistoryLines

namespace OAI

/-! # Frequency times products of the actual small slots

Slot lists retain multiplicities. These are the coefficient polynomials used
in the ancestor reversals, so their degree and magnitude bounds come from
the number and size of the original slots.
-/

namespace Ostmann

noncomputable def slotProduct {σ : Type*} : List σ → MvPolynomial σ ℤ
  | [] => 1
  | s :: slots => MvPolynomial.X s * slotProduct slots

noncomputable def frequencySlotProduct {σ : Type*} (frequency : ℤ) (slots : List σ) :
    MvPolynomial σ ℤ := MvPolynomial.C frequency * slotProduct slots

theorem slotProduct_eval {σ R : Type*} [CommRing R] (slots : List σ)
    (x : σ → R) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) x (slotProduct slots) = (slots.map x).prod := by
  induction slots with
  | nil => simp [slotProduct]
  | cons s slots ih =>
    simp only [slotProduct, map_mul, List.map_cons, List.prod_cons, ih]
    rw [MvPolynomial.eval₂Hom_X']

theorem frequencySlotProduct_eval {σ R : Type*} [CommRing R]
    (frequency : ℤ) (slots : List σ) (x : σ → R) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) x (frequencySlotProduct frequency slots) =
      (frequency : R) * (slots.map x).prod := by
  unfold frequencySlotProduct
  rw [map_mul, MvPolynomial.eval₂Hom_C, slotProduct_eval]
  rfl

theorem slotProduct_degree_le {σ : Type*} (slots : List σ) :
    (slotProduct slots).totalDegree ≤ slots.length := by
  induction slots with
  | nil => simp [slotProduct]
  | cons s slots ih =>
    have h := MvPolynomial.totalDegree_mul (MvPolynomial.X (R := ℤ) s) (slotProduct slots)
    simp only [MvPolynomial.totalDegree_X, List.length_cons] at h ⊢
    exact h.trans (by omega)

theorem frequencySlotProduct_degree_le {σ : Type*} (frequency : ℤ) (slots : List σ) :
    (frequencySlotProduct frequency slots).totalDegree ≤ slots.length := by
  have h := MvPolynomial.totalDegree_mul (MvPolynomial.C frequency) (slotProduct slots)
  simp only [MvPolynomial.totalDegree_C, zero_add] at h
  exact h.trans (slotProduct_degree_le slots)

theorem slotProduct_vars_subset {σ : Type*} [DecidableEq σ] (slots : List σ) :
    (slotProduct slots).vars ⊆ slots.toFinset := by
  induction slots with
  | nil => simp [slotProduct]
  | cons s slots ih =>
    apply (MvPolynomial.vars_mul _ _).trans
    simp only [MvPolynomial.vars_X, List.toFinset_cons, Finset.union_subset_iff]
    exact ⟨Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _),
      ih.trans (Finset.subset_insert _ _)⟩

theorem frequencySlotProduct_vars_subset {σ : Type*} [DecidableEq σ]
    (frequency : ℤ) (slots : List σ) :
    (frequencySlotProduct frequency slots).vars ⊆ slots.toFinset := by
  apply (MvPolynomial.vars_mul _ _).trans
  rw [MvPolynomial.vars_C, Finset.empty_union]
  exact slotProduct_vars_subset slots

theorem slotProduct_value_le {σ : Type*} (slots : List σ) (x : σ → ℝ)
    (U : ℝ) (hU : 0 ≤ U) (hx : ∀ s ∈ slots, |x s| ≤ U) :
    |MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x (slotProduct slots)| ≤ U ^ slots.length := by
  rw [slotProduct_eval]
  induction slots with
  | nil => simp
  | cons s slots ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, abs_mul]
    rw [pow_succ]
    exact (mul_le_mul (hx s (by simp)) (ih (fun t ht => hx t (by simp [ht])))
      (abs_nonneg _) hU).trans_eq (mul_comm _ _)

theorem frequencySlotProduct_value_le {σ : Type*} (frequency : ℤ) (slots : List σ)
    (x : σ → ℝ) (U C : ℝ) (hU : 0 ≤ U) (hfreq : |(frequency : ℝ)| ≤ C)
    (hx : ∀ s ∈ slots, |x s| ≤ U) :
    |MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x (frequencySlotProduct frequency slots)| ≤
      C * U ^ slots.length := by
  simp only [frequencySlotProduct, map_mul, MvPolynomial.eval₂Hom_C, abs_mul]
  exact mul_le_mul hfreq (slotProduct_value_le slots x U hU hx) (abs_nonneg _) (by linarith [abs_nonneg (frequency : ℝ)])

theorem frequencySlotProduct_ne_zero {σ K : Type*} [Field K]
    (frequency : ℤ) (slots : List σ) (x : σ → K)
    (hfreq : (frequency : K) ≠ 0) (hx : ∀ s ∈ slots, x s ≠ 0) :
    MvPolynomial.eval₂Hom (Int.castRingHom K) x (frequencySlotProduct frequency slots) ≠ 0 := by
  rw [frequencySlotProduct_eval]
  apply mul_ne_zero hfreq
  induction slots with
  | nil => simp
  | cons s slots ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_ne_zero (hx s (by simp)) (ih (fun t ht => hx t (by simp [ht])))

end Ostmann

end OAI
