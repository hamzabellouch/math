import Mathlib

namespace OAI


namespace Problem355.DigitCoefficients
noncomputable section
open scoped BigOperators
open Polynomial

def digitPolynomial (k : ℕ) (a : ℕ → ℤ) : ℤ[X] :=
  ∑ i ∈ Finset.range k, monomial i (a i)

lemma coeff_digitPolynomial (k u : ℕ) (a : ℕ → ℤ) :
    (digitPolynomial k a).coeff u = if u < k then a u else 0 := by
  classical
  simp [digitPolynomial, Polynomial.coeff_monomial]

lemma abs_coeff_digitPolynomial_le (k : ℕ) (a : ℕ → ℤ) (L : ℤ)
    (hL : 0 ≤ L) (ha : ∀ i < k, |a i| ≤ L) (u : ℕ) :
    |(digitPolynomial k a).coeff u| ≤ L := by
  rw [coeff_digitPolynomial]
  split_ifs with h
  · exact ha u h
  · simpa using hL

lemma abs_coeff_digitPolynomial_mul_le (k : ℕ) (a : ℕ → ℤ)
    (q : ℤ[X]) (L M : ℤ) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (ha : ∀ i < k, |a i| ≤ L) (hq : ∀ i, |q.coeff i| ≤ M) (u : ℕ) :
    |(digitPolynomial k a * q).coeff u| ≤ (k : ℤ) * L * M := by
  classical
  unfold digitPolynomial
  rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
  calc
    |∑ i ∈ Finset.range k, ((monomial i (a i)) * q).coeff u| ≤
        ∑ i ∈ Finset.range k, |((monomial i (a i)) * q).coeff u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range k, L * M := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
      split_ifs with h
      · rw [abs_mul]
        exact mul_le_mul (ha i (Finset.mem_range.mp hi)) (hq (u-i))
          (abs_nonneg _) hL
      · simp only [mul_zero, abs_zero]
        exact mul_nonneg hL hM
    _ = (k : ℤ) * L * M := by simp; ring

lemma abs_coeff_triple_digitPolynomial_le (k : ℕ) (a b c : ℕ → ℤ)
    (L : ℤ) (hL : 0 ≤ L)
    (ha : ∀ i < k, |a i| ≤ L) (hb : ∀ i < k, |b i| ≤ L)
    (hc : ∀ i < k, |c i| ≤ L) (u : ℕ) :
    |(digitPolynomial k a * digitPolynomial k b * digitPolynomial k c).coeff u|
      ≤ (k : ℤ)^2 * L^3 := by
  rw [mul_assoc]
  have hbc : ∀ i, |(digitPolynomial k b * digitPolynomial k c).coeff i|
      ≤ (k : ℤ) * L * L :=
    abs_coeff_digitPolynomial_mul_le k b (digitPolynomial k c) L L hL hL hb
      (abs_coeff_digitPolynomial_le k c L hL hc)
  have h := abs_coeff_digitPolynomial_mul_le k a
    (digitPolynomial k b * digitPolynomial k c) L ((k : ℤ) * L * L)
    hL (by positivity) ha hbc u
  convert h using 1; ring

def determinantPolynomial (k : ℕ) (d : Fin 3 → Fin 3 → ℕ → ℤ) : ℤ[X] :=
  Matrix.det (Matrix.of (fun i j => digitPolynomial k (d i j)))

theorem abs_coeff_determinantPolynomial_le (k : ℕ)
    (d : Fin 3 → Fin 3 → ℕ → ℤ) (L : ℤ) (hL : 0 ≤ L)
    (hd : ∀ i j v, v < k → |d i j v| ≤ L) (u : ℕ) :
    |(determinantPolynomial k d).coeff u| ≤ 6 * (k : ℤ)^2 * L^3 := by
  have ht (i j m n s t : Fin 3) := abs_le.mp
    (abs_coeff_triple_digitPolynomial_le k (d i j) (d m n) (d s t)
      L hL (hd i j) (hd m n) (hd s t) u)
  have h₁ := ht 0 0 1 1 2 2
  have h₂ := ht 0 0 1 2 2 1
  have h₃ := ht 0 1 1 0 2 2
  have h₄ := ht 0 1 1 2 2 0
  have h₅ := ht 0 2 1 0 2 1
  have h₆ := ht 0 2 1 1 2 0
  unfold determinantPolynomial
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub]
  apply abs_le.mpr
  constructor <;> nlinarith

lemma eval_digitPolynomial (k : ℕ) (a : ℕ → ℤ) (B : ℤ) :
    (digitPolynomial k a).eval B = ∑ i ∈ Finset.range k, a i * B^i := by
  simp [digitPolynomial, Polynomial.eval_finsetSum]

lemma eval_determinantPolynomial (k : ℕ) (d : Fin 3 → Fin 3 → ℕ → ℤ) (B : ℤ) :
    (determinantPolynomial k d).eval B =
      Matrix.det (Matrix.of (fun i j => ∑ v ∈ Finset.range k, d i j v * B^v)) := by
  simp only [determinantPolynomial, Matrix.det_fin_three, Matrix.of_apply, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_mul, eval_digitPolynomial]

lemma det_monomial_rows {R : Type*} [CommRing R]
    (v : Fin 3 → ℕ) (A : Matrix (Fin 3) (Fin 3) R) :
    Matrix.det (Matrix.of (fun i j => monomial (v i) (A i j))) =
      monomial (v 0 + v 1 + v 2) A.det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply, Polynomial.monomial_mul_monomial, map_add, map_sub]

lemma determinantPolynomial_eq_sum (k : ℕ) (d : Fin 3 → Fin 3 → ℕ → ℤ) :
    determinantPolynomial k d =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range k),
        monomial (v 0 + v 1 + v 2) (Matrix.det (Matrix.of (fun i j => d i j (v i)))) := by
  classical
  have h := (Matrix.detRowAlternating (n := Fin 3) (R := ℤ[X])).toMultilinearMap.map_sum_finset
    (fun i v j => monomial v (d i j v)) (fun _ => Finset.range k)
  change Matrix.det (Matrix.of (fun i => ∑ v ∈ Finset.range k, fun j => monomial v (d i j v))) = _ at h
  have hrows : (fun i => ∑ v ∈ Finset.range k, fun j => monomial v (d i j v)) =
      (fun i j => digitPolynomial k (d i j)) := by
    funext i j
    simp only [Finset.sum_apply, digitPolynomial]
  rw [hrows] at h
  change determinantPolynomial k d = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro v hv
  exact det_monomial_rows v (fun i j => d i j (v i))

lemma coeff_determinantPolynomial_eq_sum (k u : ℕ)
    (d : Fin 3 → Fin 3 → ℕ → ℤ) :
    (determinantPolynomial k d).coeff u =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range k),
        if v 0 + v 1 + v 2 = u then Matrix.det (Matrix.of (fun i j => d i j (v i))) else 0 := by
  rw [determinantPolynomial_eq_sum, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]

lemma coeff_det_sum_monomial {R : Type*} [CommRing R] {α : Type*}
    (s : Finset α) (pos : Fin 3 → α → ℕ) (d : Fin 3 → Fin 3 → α → R) (u : ℕ) :
    (Matrix.det (Matrix.of (fun i j => ∑ a ∈ s, monomial (pos i a) (d i j a)))).coeff u =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin 3 => s),
        if pos 0 (v 0) + pos 1 (v 1) + pos 2 (v 2) = u
        then Matrix.det (Matrix.of (fun i j => d i j (v i))) else 0 := by
  classical
  have h := (Matrix.detRowAlternating (n := Fin 3) (R := R[X])).toMultilinearMap.map_sum_finset
    (fun i a j => monomial (pos i a) (d i j a)) (fun _ => s)
  change Matrix.det (Matrix.of (fun i => ∑ a ∈ s, fun j => monomial (pos i a) (d i j a))) = _ at h
  have hrows : (fun i => ∑ a ∈ s, fun j => monomial (pos i a) (d i j a)) =
      (fun i j => ∑ a ∈ s, monomial (pos i a) (d i j a)) := by
    funext i j
    simp only [Finset.sum_apply]
  rw [hrows] at h
  rw [h, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro v hv
  change (Matrix.det (Matrix.of (fun i j => monomial (pos i (v i)) (d i j (v i))))).coeff u = _
  have hdet := det_monomial_rows (fun i => pos i (v i))
    (Matrix.of (fun i j => d i j (v i)))
  simp only [Matrix.of_apply] at hdet
  rw [hdet]
  simp only [Polynomial.coeff_monomial]

end
end Problem355.DigitCoefficients

end OAI
