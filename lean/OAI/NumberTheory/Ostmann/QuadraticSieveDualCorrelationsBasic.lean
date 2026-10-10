import OAI.NumberTheory.Ostmann.QuadraticSieveComplementCorrelationsError
import OAI.NumberTheory.Ostmann.QuadraticSieveDualLeadingTerm
import OAI.NumberTheory.Ostmann.QuadraticSieveDualPoissonTailScale
import OAI.NumberTheory.Ostmann.QuadraticSieveGaussRowsBasic

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate MeasureTheory Set
open scoped SchwartzMap FourierTransform ArithmeticFunction.Moebius

noncomputable def dualSignedSquareWeight (W : 𝓢(ℝ, ℂ)) (s : ℤ) : 𝓢(ℝ, ℂ) :=
  if hs : s = 0 then 0 else squarePullback (𝓕 W) (s : ℝ) (by exact_mod_cast hs)

theorem dualSignedSquareWeight_eq (W : 𝓢(ℝ, ℂ)) (s : ℤ) (hs : s ≠ 0) :
    dualSignedSquareWeight W s = squarePullback (𝓕 W) (s : ℝ) (by exact_mod_cast hs) := by
  simp only [dualSignedSquareWeight, dite_eq_right hs]

noncomputable def dualCorrelationGaussFactor (M : ℝ) (e q : ℕ) : ℂ :=
  ((M/e : ℝ) : ℂ) * jacobiGaussRatio q * (μ e : ℂ)

theorem dualCorrelationGaussFactor_eq (M : ℝ) (e q : ℕ) [NeZero q] :
    dualCorrelationGaussFactor M e q =
      (μ e : ℂ) * ((M/(e*q) : ℝ) : ℂ) *
        gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar := by
  rw [dualCorrelationGaussFactor, jacobiGaussRatio_eq]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

noncomputable def dualCorrelationPrefixTerm (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K q : ℕ) : ℂ :=
  ∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers, ∑ b ∈ oddSquarefreeUpTo K,
    dualCorrelationGaussFactor M e q * (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ) *
      dualSquareSum W (s : ℝ) e M b q

noncomputable def dualCorrelationTailTerm (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ q : ℕ) (K : ℝ) : ℂ :=
  ∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers,
    dualCorrelationGaussFactor M e q * (jacobiSym (e : ℤ) q : ℂ) *
      dualSquarefreeTail W s e M q K

noncomputable def dualSecondSquareMain (W : 𝓢(ℝ, ℂ)) (M : ℝ) (e : ℕ) (s : ℤ) (b q : ℕ)
    (X₁ X₂ L : ℕ → ℕ → ℝ) : ℂ :=
  (1/2 : ℂ) * coprimePoissonMain (dualSignedSquareWeight W s) q
    (Real.sqrt ((e : ℝ)*q/(M*b))) (X₁ e b) (X₂ e b) (L e b)

noncomputable def dualCorrelationMainTerm (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K q : ℕ)
    (X₁ X₂ L : ℕ → ℕ → ℝ) : ℂ :=
  ∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers, ∑ b ∈ oddSquarefreeUpTo K,
    dualCorrelationGaussFactor M e q * (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ) *
      dualSecondSquareMain W M e s b q X₁ X₂ L

noncomputable def dualCorrelationRemainderTerm (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K q : ℕ)
    (X₁ X₂ L : ℕ → ℕ → ℝ) : ℂ :=
  ∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers, ∑ b ∈ oddSquarefreeUpTo K,
    dualCorrelationGaussFactor M e q * (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ) *
      (dualSquareSum W (s : ℝ) e M b q - dualSecondSquareMain W M e s b q X₁ X₂ L)

theorem dualCorrelationPrefixTerm_eq (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K q : ℕ) [NeZero q] :
    dualCorrelationPrefixTerm W M Δ K q = dualPoissonPrefix W M (2*Δ) q K := by
  simp only [dualCorrelationPrefixTerm, dualPoissonPrefix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro b hb
  rw [dualCorrelationGaussFactor_eq, mul_assoc (e : ℤ), jacobiSym.mul_left, Int.cast_mul]
  ring

theorem dualCorrelationTailTerm_eq (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ q : ℕ) [NeZero q] (K : ℝ) :
    dualCorrelationTailTerm W M Δ q K = dualPoissonTail W M (2*Δ) q K := by
  simp only [dualCorrelationTailTerm, dualPoissonTail, dualCorrelationGaussFactor_eq]

theorem dualCorrelationPrefixTerm_split (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K q : ℕ)
    (X₁ X₂ L : ℕ → ℕ → ℝ) :
    dualCorrelationPrefixTerm W M Δ K q = dualCorrelationMainTerm W M Δ K q X₁ X₂ L +
      dualCorrelationRemainderTerm W M Δ K q X₁ X₂ L := by
  simp only [dualCorrelationPrefixTerm, dualCorrelationMainTerm, dualCorrelationRemainderTerm,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem coprime_quadratic_poisson_second_main {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) (hq1 : 1 < q) (W : 𝓢(ℝ, ℂ))
    (M : ℝ) (hM : 0 < M) (Δ K : ℕ) (hΔ : Δ ≠ 0) (X₁ X₂ L : ℕ → ℕ → ℝ) :
    (∑' m : ℤ, if Nat.Coprime m.natAbs (2*Δ) then
      (jacobiSym m q : ℂ) * W ((m : ℝ)/M) else 0) =
      dualCorrelationMainTerm W M Δ K q X₁ X₂ L +
        dualCorrelationRemainderTerm W M Δ K q X₁ X₂ L + dualCorrelationTailTerm W M Δ q K := by
  rw [coprime_quadratic_poisson_prefix_tail hq hsq hq1 (2*Δ)
    (mul_ne_zero (by omega) hΔ) M hM W K,
    ← dualCorrelationPrefixTerm_eq, ← dualCorrelationTailTerm_eq,
    dualCorrelationPrefixTerm_split W M Δ K q X₁ X₂ L]

end Ostmann.QuadraticSieve

end OAI
