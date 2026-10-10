import OAI.NumberTheory.Ostmann.Construction.HistoryResidueGate
import OAI.NumberTheory.Ostmann.Characters.PolynomialRangeGuards
import OAI.NumberTheory.Ostmann.Arithmetic.HarmonicPeriodicBound

namespace OAI

/-! # One-sided cancellation with the literal history support conditions -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def supportedHistoryAmplitude {σ I : Type*} [Fintype I] {n : ℕ}
    (N : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ) (a : σ → ℤ) (i : σ)
    (F : Fin n → ClippedPolynomialFactor) (x : ℤ) : ℂ :=
  (if ∀ j, smallDivisionTest
    (MvPolynomial.eval₂ (RingHom.id ℤ) (Function.update a i x) (N j)) (d j) (s j) then 1 else 0) *
    ((if ∀ j, (F j).polynomial.eval (x : ℝ) ∈ Set.Icc (F j).lo (F j).hi then 1 else 0) *
      ∏ j, (F j).profile ((F j).polynomial.eval (x : ℝ)))

theorem supportedHistoryAmplitude_eq {σ I : Type*} [Fintype I] {n : ℕ}
    (N : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ) (a : σ → ℤ) (i : σ)
    (F : Fin n → ClippedPolynomialFactor) (M : ℕ) [NeZero M]
    (hd : ∀ j, d j ≠ 0) (hdiv : ∀ j, d j * s j ∣ (M : ℤ)) (x : ℤ) :
    supportedHistoryAmplitude N d s a i F x =
      clearedHistoryResidueGate N d s a i M (x : ZMod M) *
        polynomialAmplitude F (polynomialRangeBounds F) (polynomialRangeKeep n) (x : ℝ) := by
  rw [clearedHistoryResidueGate_exact N d s a i M hd hdiv x, polynomialAmplitude_range]
  rfl

/-- All residue gates and sharp smooth-argument ranges are the actual tests
on the sampled integers. No hypothesis asserting their regularity is needed. -/
theorem harmonic_supported_history_bound {σ I : Type*} [Fintype I] {n : ℕ}
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (χ : ∀ q : Q, DirichletCharacter ℂ (q : ℕ)) (hnonprincipal : ∀ q, χ q ≠ 1)
    (a M K : ℕ) [NeZero M] (ha : 0 < a) (hM : ∀ q : Q, M.Coprime (q : ℕ))
    (hlow : ∀ p ∈ P, a ≤ p) (hhigh : ∀ p ∈ P, p < a + K * M)
    (b : ℝ) (hb : 0 < b) (hbQ : ∀ q ∈ Q, b ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (N : Q → I → MvPolynomial σ ℤ) (d : Q → I → ℤ) (s : Q → I → ℕ)
    (fixed : Q → σ → ℤ) (coord : σ)
    (hd : ∀ q j, d q j ≠ 0) (hdiv : ∀ q j, d q j * s q j ∣ (M : ℤ))
    (F : Q → Fin n → ClippedPolynomialFactor) (B : ℝ) (D Bq : ℕ)
    (hB : 0 ≤ B) (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hdegree : ∀ q, (∑ j, (F q j).polynomial.natDegree) ≤ D)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq)
    (U : P → ℂ) (V : Q → ℂ) (hU : ∀ p, ‖U p‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      (U p * ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * V q *
        (χ q ((p : ℕ) : ZMod (q : ℕ)) *
          supportedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) (p : ℕ)))‖ ^ 2 ≤
      (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (((K * M : ℕ) : ℝ) / a * B ^ 2) +
          (M : ℝ) * ((3 ^ (2 * (3 * D)) : ℕ) * (2 * (a : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  have he (q : Q) (p : P) : supportedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) (p : ℕ) =
      clearedHistoryResidueGate (N q) (d q) (s q) (fixed q) coord M ((p : ℕ) : ZMod M) *
        polynomialAmplitude (F q) (polynomialRangeBounds (F q)) (polynomialRangeKeep n) (p : ℝ) := by
    simpa only [Int.cast_natCast] using supportedHistoryAmplitude_eq
      (N q) (d q) (s q) (fixed q) coord (F q) M (hd q) (hdiv q) (p : ℕ)
  simp_rw [he]
  apply harmonic_periodic_polynomial_one_sided_bound P Q hprime χ hnonprincipal a M K ha hM
    (fun q => clearedHistoryResidueGate (N q) (d q) (s q) (fixed q) coord M)
    (fun q => clearedHistoryResidueGate_norm (N q) (d q) (s q) (fixed q) coord M)
    hlow hhigh b hb hbQ hPmass hQmass F (fun q => polynomialRangeBounds (F q))
    (fun _ => polynomialRangeKeep n) B (3 * D) Bq hB hbudget _ hBq U V hU hV
  intro q
  exact (polynomialRange_complexity (F q)).trans (Nat.mul_le_mul_left 3 (hdegree q))

end Ostmann

end OAI
