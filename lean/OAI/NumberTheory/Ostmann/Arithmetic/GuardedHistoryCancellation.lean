import OAI.NumberTheory.Ostmann.Arithmetic.SupportedHistoryCancellation

namespace OAI

/-! # One-sided cancellation retaining all polynomial history tests -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def guardedHistoryAmplitude {σ I : Type*} [Fintype I] {n t : ℕ}
    (N : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ) (a : σ → ℤ) (i : σ)
    (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (x : ℤ) : ℂ :=
  (if ∀ j, smallDivisionTest
    (MvPolynomial.eval₂ (RingHom.id ℤ) (Function.update a i x) (N j)) (d j) (s j) then 1 else 0) *
    polynomialAmplitude F H keep (x : ℝ)

theorem guardedHistoryAmplitude_residue {σ I : Type*} [Fintype I] {n t : ℕ}
    (N : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ) (a : σ → ℤ) (i : σ)
    (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (M : ℕ) [NeZero M]
    (hd : ∀ j, d j ≠ 0) (hdiv : ∀ j, d j * s j ∣ (M : ℤ)) (x : ℤ) :
    guardedHistoryAmplitude N d s a i F H keep x =
      clearedHistoryResidueGate N d s a i M (x : ZMod M) * polynomialAmplitude F H keep (x : ℝ) := by
  rw [clearedHistoryResidueGate_exact N d s a i M hd hdiv x]
  rfl

theorem harmonic_guarded_history_bound {σ I : Type*} [Fintype I] {n t : ℕ}
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (χ : ∀ q : Q, DirichletCharacter ℂ (q : ℕ)) (hnonprincipal : ∀ q, χ q ≠ 1)
    (a M K : ℕ) [NeZero M] (ha : 0 < a) (hM : ∀ q : Q, M.Coprime (q : ℕ))
    (hlow : ∀ p ∈ P, a ≤ p) (hhigh : ∀ p ∈ P, p < a + K * M)
    (b : ℝ) (hb : 0 < b) (hbQ : ∀ q ∈ Q, b ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (N : Q → I → MvPolynomial σ ℤ) (d : Q → I → ℤ) (s : Q → I → ℕ)
    (fixed : Q → σ → ℤ) (coord : σ)
    (hd : ∀ q j, d q j ≠ 0) (hdiv : ∀ q j, d q j * s q j ∣ (M : ℤ))
    (F : Q → Fin n → ClippedPolynomialFactor) (H : Q → Fin t → Polynomial ℝ)
    (keep : Q → (Fin t → Bool) → Bool) (B : ℝ) (R Bq : ℕ)
    (hB : 0 ≤ B) (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq)
    (U : P → ℂ) (V : Q → ℂ) (hU : ∀ p, ‖U p‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      (U p * ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * V q *
        (χ q ((p : ℕ) : ZMod (q : ℕ)) *
          guardedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) (H q) (keep q) (p : ℕ)))‖ ^ 2 ≤
      (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (((K * M : ℕ) : ℝ) / a * B ^ 2) +
          (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (a : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  have he (q : Q) (p : P) : guardedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord
      (F q) (H q) (keep q) (p : ℕ) =
      clearedHistoryResidueGate (N q) (d q) (s q) (fixed q) coord M ((p : ℕ) : ZMod M) *
        polynomialAmplitude (F q) (H q) (keep q) (p : ℝ) := by
    simpa only [Int.cast_natCast] using guardedHistoryAmplitude_residue
      (N q) (d q) (s q) (fixed q) coord (F q) (H q) (keep q) M (hd q) (hdiv q) (p : ℕ)
  simp_rw [he]
  exact harmonic_periodic_polynomial_one_sided_bound P Q hprime χ hnonprincipal a M K ha hM
    (fun q => clearedHistoryResidueGate (N q) (d q) (s q) (fixed q) coord M)
    (fun q => clearedHistoryResidueGate_norm (N q) (d q) (s q) (fixed q) coord M)
    hlow hhigh b hb hbQ hPmass hQmass F H keep B R Bq hB hbudget hcomplexity hBq U V hU hV

end Ostmann

end OAI
