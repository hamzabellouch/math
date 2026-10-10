import OAI.Geometry.HeilbronnTriangle.PrescribedDigits
import OAI.Geometry.HeilbronnTriangle.DigitObstruction

namespace OAI


noncomputable section
namespace Problem355.EncodedDeterminant

open Polynomial DigitCoefficients DesignatedCoefficient DigitEncoding

theorem encoded_polynomial_obstruction {R : Type*} [CommRing R]
    (φ : ℤ →+* R) (T : ℕ) (B L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * ((T ^ 2 + 1 : ℕ) : ℤ) ^ 2 * L ^ 3 < B)
    (d : Fin 3 → Fin 3 → ℕ → ℤ) (f : Fin 3 → Fin T → Fin 3 → R)
    (hd : ∀ i j v, v < T ^ 2 + 1 → |d i j v| ≤ L)
    (hdesignated : ∀ i j a, φ (d i j (position T i a)) = f i a j)
    (hzero : ∀ i j n, n < T ^ 2 + 1 →
      (∀ a : Fin T, position T i a ≠ n) → φ (d i j n) = 0)
    (hne : (∑ a : Fin T, Matrix.det (fun i j => f i a j)) ≠ 0)
    {x : ℤ}
    (hx : x ≡ (determinantPolynomial (T ^ 2 + 1) d).eval B
      [ZMOD B ^ (T ^ 2 + 1)]) :
    B ^ (T ^ 2) / 2 < |x| := by
  apply polynomial_obstruction (determinantPolynomial (T ^ 2 + 1) d)
    B hB (T ^ 2) _ _ hx
  · intro n hn
    exact coefficient_bound_normalized hbase
      (abs_coeff_determinantPolynomial_le (T ^ 2 + 1) d L hL hd n)
  · exact digit_det_designated_coefficient_ne_zero φ T d f hdesignated hzero hne

theorem encoded_integer_determinant_obstruction {R : Type*} [CommRing R]
    (φ : ℤ →+* R) (T : ℕ) (B L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * ((T ^ 2 + 1 : ℕ) : ℤ) ^ 2 * L ^ 3 < B)
    (d : Fin 3 → Fin 3 → ℕ → ℤ) (f : Fin 3 → Fin T → Fin 3 → R)
    (hd : ∀ i j v, v < T ^ 2 + 1 → |d i j v| ≤ L)
    (hdesignated : ∀ i j a, φ (d i j (position T i a)) = f i a j)
    (hzero : ∀ i j n, n < T ^ 2 + 1 →
      (∀ a : Fin T, position T i a ≠ n) → φ (d i j n) = 0)
    (hne : (∑ a : Fin T, Matrix.det (fun i j => f i a j)) ≠ 0)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hAC : ∀ i j, A i j ≡ ∑ v ∈ Finset.range (T ^ 2 + 1), d i j v * B ^ v
      [ZMOD B ^ (T ^ 2 + 1)]) :
    B ^ (T ^ 2) / 2 < |A.det| := by
  apply encoded_polynomial_obstruction φ T B L hB hL hbase d f hd hdesignated hzero hne
  rw [eval_determinantPolynomial]
  exact determinant_modEq hAC

theorem encoded_mixed_determinant_obstruction {R : Type*} [CommRing R]
    (φ : ℤ →+* R) (T B : ℕ) (L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * ((T ^ 2 + 1 : ℕ) : ℤ) ^ 2 * L ^ 3 < B)
    (d : Fin 3 → Fin 3 → ℕ → ℤ) (f : Fin 3 → Fin T → Fin 3 → R)
    (hd : ∀ i j v, v < T ^ 2 + 1 → |d i j v| ≤ L)
    (hdesignated : ∀ i j a, φ (d i j (position T i a)) = f i a j)
    (hzero : ∀ i j n, n < T ^ 2 + 1 →
      (∀ a : Fin T, position T i a ≠ n) → φ (d i j n) = 0)
    (hne : (∑ a : Fin T, Matrix.det (fun i j => f i a j)) ≠ 0)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (G : Matrix.SpecialLinearGroup (Fin 3) (ZMod (B ^ (T ^ 2 + 1))))
    (hAC : A.map (Int.castRingHom (ZMod (B ^ (T ^ 2 + 1)))) =
      (G : Matrix (Fin 3) (Fin 3) (ZMod (B ^ (T ^ 2 + 1)))) *
        (Matrix.map (fun i j => ∑ v ∈ Finset.range (T ^ 2 + 1), d i j v * (B : ℤ) ^ v)
          (Int.castRingHom (ZMod (B ^ (T ^ 2 + 1)))))) :
    (B : ℤ) ^ (T ^ 2) / 2 < |A.det| := by
  apply encoded_polynomial_obstruction φ T (B : ℤ) L (by exact_mod_cast hB)
    hL hbase d f hd hdesignated hzero hne
  rw [eval_determinantPolynomial]
  have hm := determinant_modEq_of_specialLinear (B ^ (T ^ 2 + 1)) G A
    (Matrix.of fun i j => ∑ v ∈ Finset.range (T ^ 2 + 1), d i j v * (B : ℤ) ^ v) hAC
  simpa only [Nat.cast_pow] using hm

end Problem355.EncodedDeterminant

end

end OAI
