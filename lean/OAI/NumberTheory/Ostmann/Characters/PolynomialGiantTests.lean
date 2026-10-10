import OAI.NumberTheory.Ostmann.Characters.PolynomialGiantRows

namespace OAI

/-! # Cleared coefficient and minor tests for the giant lines -/

namespace Ostmann

noncomputable section

structure PolynomialGiantLine (σ : Type*) where
  a : MvPolynomial σ ℤ
  b : MvPolynomial σ ℤ
  denominator : MvPolynomial σ ℤ

/-- The numerator `v * Hminus - w * Hplus`, with the ancestor denominator
still cleared. The current compensation variable does not occur here. -/
def PolynomialGiantRows.numeratorLine {σ : Type*} (T : PolynomialGiantRows σ)
    (v w : MvPolynomial σ ℤ) : PolynomialGiantLine σ :=
  ⟨v * T.rows.c - w * T.rows.a, v * T.rows.d - w * T.rows.b, T.denominator⟩

namespace PolynomialGiantLine

variable {σ : Type*}

def normalized {K : Type*} [Field K] (L : PolynomialGiantLine σ)
    (φ : MvPolynomial σ ℤ →+* K) : K × K :=
  (φ L.a / φ L.denominator, φ L.b / φ L.denominator)

def minor (L M : PolynomialGiantLine σ) : MvPolynomial σ ℤ := L.a * M.b - L.b * M.a

theorem normalized_zero_iff {K : Type*} [Field K] (L : PolynomialGiantLine σ)
    (φ : MvPolynomial σ ℤ →+* K) (hden : φ L.denominator ≠ 0) :
    ((L.normalized φ).1 = 0 ↔ φ L.a = 0) ∧
      ((L.normalized φ).2 = 0 ↔ φ L.b = 0) := by
  simp only [normalized, div_eq_zero_iff, hden, or_false, and_self]

theorem normalized_minor {K : Type*} [Field K] (L M : PolynomialGiantLine σ)
    (φ : MvPolynomial σ ℤ →+* K)
    (hL : φ L.denominator ≠ 0) (hM : φ M.denominator ≠ 0) :
    (L.normalized φ).1 * (M.normalized φ).2 -
      (L.normalized φ).2 * (M.normalized φ).1 =
      φ (L.minor M) / (φ L.denominator * φ M.denominator) := by
  simp only [normalized, minor, map_sub, map_mul]
  field_simp

theorem normalized_minor_zero_iff {K : Type*} [Field K] (L M : PolynomialGiantLine σ)
    (φ : MvPolynomial σ ℤ →+* K)
    (hL : φ L.denominator ≠ 0) (hM : φ M.denominator ≠ 0) :
    ((L.normalized φ).1 * (M.normalized φ).2 -
      (L.normalized φ).2 * (M.normalized φ).1 = 0) ↔ φ (L.minor M) = 0 := by
  rw [normalized_minor L M φ hL hM]
  simp only [div_eq_zero_iff, mul_ne_zero hL hM, or_false]

end PolynomialGiantLine

/-- Normalizing the cleared numerator gives its actual two coefficients. -/
theorem PolynomialGiantRows.normalized_numeratorLine {σ K : Type*} [Field K]
    (T : PolynomialGiantRows σ) (v w : MvPolynomial σ ℤ)
    (φ : MvPolynomial σ ℤ →+* K) (hd : φ T.denominator ≠ 0) :
    (T.numeratorLine v w).normalized φ =
      (φ v * (T.normalized φ).c - φ w * (T.normalized φ).a,
        φ v * (T.normalized φ).d - φ w * (T.normalized φ).b) := by
  apply Prod.ext <;>
    simp only [PolynomialGiantLine.normalized, PolynomialGiantRows.numeratorLine,
      PolynomialGiantRows.normalized, map_sub, map_mul] <;> field_simp

/-- Reduction of an integer polynomial evaluation commutes with casting to a
prime residue ring. Thus these tests are genuine integer divisibility tests. -/
theorem integerPolynomial_cast_eval {σ : Type*} (x : σ → ℤ) (F : MvPolynomial σ ℤ) (p : ℕ) :
    ((MvPolynomial.eval₂Hom (RingHom.id ℤ) x F : ℤ) : ZMod p) =
      MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p)) (fun i => (x i : ZMod p)) F := by
  simpa [Int.castRingHom] using
    (MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom (ZMod p)) F)

/-- A cleared polynomial vanishes in the prime field exactly when the prime
divides its actual integer evaluation. -/
theorem integerPolynomial_mod_zero_iff {σ : Type*} (x : σ → ℤ)
    (F : MvPolynomial σ ℤ) (p : ℕ) :
    MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p)) (fun i => (x i : ZMod p)) F = 0 ↔
      (p : ℤ) ∣ MvPolynomial.eval₂Hom (RingHom.id ℤ) x F := by
  rw [← integerPolynomial_cast_eval, ZMod.intCast_zmod_eq_zero_iff_dvd]

end

end Ostmann

end OAI
