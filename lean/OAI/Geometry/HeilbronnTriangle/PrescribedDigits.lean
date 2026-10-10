import OAI.Geometry.HeilbronnTriangle.DesignatedCoefficient
import OAI.Geometry.HeilbronnTriangle.DeterminantCoefficients

namespace OAI


noncomputable section
namespace Problem355.DesignatedCoefficient
open Polynomial

lemma last_position_product_le (T : ℕ) (a : Fin T) :
    (T + 1) * a.val ≤ T ^ 2 := by
  have ha : a.val + 1 ≤ T := a.isLt
  have h := Nat.mul_le_mul_left (T + 1) ha
  nlinarith

lemma position_injective (T : ℕ) (i : Fin 3) :
    Function.Injective (position T i) := by
  intro a b hab
  apply Fin.ext
  have hT : 0 < T := Nat.zero_lt_of_lt a.isLt
  fin_cases i
  · exact hab
  · change T * a.val = T * b.val at hab
    nlinarith
  · change T ^ 2 - (T + 1) * a.val = T ^ 2 - (T + 1) * b.val at hab
    have ha := Nat.sub_add_cancel (last_position_product_le T a)
    have hb := Nat.sub_add_cancel (last_position_product_le T b)
    nlinarith

lemma position_lt (T : ℕ) (i : Fin 3) (a : Fin T) :
    position T i a < T ^ 2 + 1 := by
  have hT : 0 < T := Nat.zero_lt_of_lt a.isLt
  fin_cases i
  · change a.val < T ^ 2 + 1
    have ha := a.isLt
    nlinarith
  · change T * a.val < T ^ 2 + 1
    have ha := Nat.mul_lt_mul_of_pos_left a.isLt hT
    nlinarith
  · change T ^ 2 - (T + 1) * a.val < T ^ 2 + 1
    exact Nat.lt_succ_of_le (Nat.sub_le _ _)

theorem map_eq_polynomialMatrix_of_coefficients {R : Type*} [CommRing R]
    (φ : ℤ →+* R) (T : ℕ) (P : Matrix (Fin 3) (Fin 3) ℤ[X])
    (f : Fin 3 → Fin T → Fin 3 → R)
    (hdesignated : ∀ i j a, φ ((P i j).coeff (position T i a)) = f i a j)
    (hzero : ∀ i j n, (∀ a : Fin T, position T i a ≠ n) →
      φ ((P i j).coeff n) = 0) :
    ∀ i j, (P i j).map φ = polynomialMatrix T f i j := by
  classical
  intro i j
  ext n
  rw [Polynomial.coeff_map]
  change φ ((P i j).coeff n) =
    (∑ a : Fin T, monomial (position T i a) (f i a j)).coeff n
  rw [Polynomial.finsetSum_coeff]
  by_cases hn : ∃ a : Fin T, position T i a = n
  · obtain ⟨a, rfl⟩ := hn
    rw [hdesignated]
    symm
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hba
      rw [Polynomial.coeff_monomial, ite_eq_right]
      exact fun h => hba (position_injective T i h)
    · simp
  · have hn' : ∀ a : Fin T, position T i a ≠ n := by simpa using hn
    rw [hzero i j n hn']
    symm
    apply Finset.sum_eq_zero
    intro a ha
    rw [Polynomial.coeff_monomial, ite_eq_right (hn' a)]

theorem digitPolynomial_map_eq {R : Type*} [CommRing R] (φ : ℤ →+* R)
    (T : ℕ) (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (f : Fin 3 → Fin T → Fin 3 → R)
    (hdesignated : ∀ i j a, φ (d i j (position T i a)) = f i a j)
    (hzero : ∀ i j n, n < T ^ 2 + 1 →
      (∀ a : Fin T, position T i a ≠ n) → φ (d i j n) = 0) :
    ∀ i j, (DigitCoefficients.digitPolynomial (T ^ 2 + 1) (d i j)).map φ =
      polynomialMatrix T f i j := by
  apply map_eq_polynomialMatrix_of_coefficients φ T
    (fun i j => DigitCoefficients.digitPolynomial (T ^ 2 + 1) (d i j)) f
  · intro i j a
    rw [DigitCoefficients.coeff_digitPolynomial, ite_eq_left (position_lt T i a)]
    exact hdesignated i j a
  · intro i j n hn
    rw [DigitCoefficients.coeff_digitPolynomial]
    split_ifs with hnk
    · exact hzero i j n hnk hn
    · exact map_zero φ

theorem digit_det_designated_coefficient_ne_zero {R : Type*} [CommRing R]
    (φ : ℤ →+* R) (T : ℕ) (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (f : Fin 3 → Fin T → Fin 3 → R)
    (hdesignated : ∀ i j a, φ (d i j (position T i a)) = f i a j)
    (hzero : ∀ i j n, n < T ^ 2 + 1 →
      (∀ a : Fin T, position T i a ≠ n) → φ (d i j n) = 0)
    (hne : (∑ a : Fin T, Matrix.det (fun i j => f i a j)) ≠ 0) :
    (DigitCoefficients.determinantPolynomial (T ^ 2 + 1) d).coeff (T ^ 2) ≠ 0 := by
  exact designated_coefficient_ne_zero φ T
    (fun i j => DigitCoefficients.digitPolynomial (T ^ 2 + 1) (d i j)) f
    (digitPolynomial_map_eq φ T d f hdesignated hzero) hne

end Problem355.DesignatedCoefficient

end

end OAI
