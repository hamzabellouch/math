import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrelations

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory Set
open scoped SchwartzMap FourierTransform ArithmeticFunction.Moebius

noncomputable def dualCorrelationFiniteForm (M : ℝ) (Δ K q : ℕ)
    (F : ℕ → ℤ → ℕ → ℂ) : ℂ :=
  ∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers, ∑ b ∈ oddSquarefreeUpTo K,
    dualCorrelationGaussFactor M e q * (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ) * F e s b

noncomputable def dualSquareLeading (W : 𝓢(ℝ, ℂ)) (M : ℝ) (e : ℕ) (s : ℤ) (b q : ℕ) : ℂ :=
  (1/2 : ℂ) * ((Nat.totient q : ℂ)/(q : ℂ)) * (Real.sqrt ((e : ℝ)*q/(M*b)) : ℂ) *
    (∫ x : ℝ, dualSignedSquareWeight W s x)

noncomputable def dualSquareZeroCorrection (W : 𝓢(ℝ, ℂ)) (q : ℕ) (s : ℤ) (X₂ : ℝ) : ℂ :=
  -(1/2 : ℂ) * dualSignedSquareWeight W s 0 *
    ∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X₂), (μ d : ℂ)

noncomputable def dualSquareLargeCorrection (W : 𝓢(ℝ, ℂ)) (M : ℝ)
    (e : ℕ) (s : ℤ) (b q : ℕ) (X₂ : ℝ) : ℂ :=
  -(1/2 : ℂ) * (Real.sqrt ((e : ℝ)*q/(M*b)) : ℂ) *
    (∫ x : ℝ, dualSignedSquareWeight W s x) *
    ∑ d ∈ q.divisors.filter (fun d : ℕ => X₂ < (d : ℝ)), (μ d : ℂ)/(d : ℂ)

noncomputable def dualSquareFourierCorrection (W : 𝓢(ℝ, ℂ)) (M : ℝ)
    (e : ℕ) (s : ℤ) (b q : ℕ) (X₁ X₂ L : ℝ) : ℂ :=
  (1/2 : ℂ) * ∑ d ∈ q.divisors.filter (fun d : ℕ => X₁ < (d : ℝ) ∧ (d : ℝ) ≤ X₂),
    (μ d : ℂ) * ((Real.sqrt ((e : ℝ)*q/(M*b))/d : ℝ) : ℂ) *
      ∑ l ∈ nonzeroIntegerCutoff L,
        𝓕 (dualSignedSquareWeight W s) ((l : ℝ)*(Real.sqrt ((e : ℝ)*q/(M*b))/d))

noncomputable def dualCorrelationLeadingTerm (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K q : ℕ) : ℂ :=
  dualCorrelationFiniteForm M Δ K q (fun e s b => dualSquareLeading W M e s b q)

noncomputable def dualCorrelationZeroTerm (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K q : ℕ)
    (X₂ : ℕ → ℕ → ℝ) : ℂ :=
  dualCorrelationFiniteForm M Δ K q (fun e s b => dualSquareZeroCorrection W q s (X₂ e b))

noncomputable def dualCorrelationLargeTerm (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K q : ℕ)
    (X₂ : ℕ → ℕ → ℝ) : ℂ :=
  dualCorrelationFiniteForm M Δ K q (fun e s b => dualSquareLargeCorrection W M e s b q (X₂ e b))

noncomputable def dualCorrelationFourierTerm (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K q : ℕ)
    (X₁ X₂ L : ℕ → ℕ → ℝ) : ℂ :=
  dualCorrelationFiniteForm M Δ K q (fun e s b =>
    dualSquareFourierCorrection W M e s b q (X₁ e b) (X₂ e b) (L e b))

theorem dualCorrelationMainTerm_parts (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K q : ℕ)
    (X₁ X₂ L : ℕ → ℕ → ℝ) :
    dualCorrelationMainTerm W M Δ K q X₁ X₂ L = dualCorrelationLeadingTerm W M Δ K q +
      dualCorrelationZeroTerm W M Δ K q X₂ + dualCorrelationLargeTerm W M Δ K q X₂ +
      dualCorrelationFourierTerm W M Δ K q X₁ X₂ L := by
  simp only [dualCorrelationMainTerm, dualCorrelationLeadingTerm, dualCorrelationZeroTerm,
    dualCorrelationLargeTerm, dualCorrelationFourierTerm, dualCorrelationFiniteForm,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro b hb
  unfold dualSecondSquareMain dualSquareLeading dualSquareZeroCorrection
    dualSquareLargeCorrection dualSquareFourierCorrection coprimePoissonMain
  ring

theorem dualCorrelationLeadingTerm_eq (W : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) (M : ℝ) (hM : 0 < M) (Δ K q : ℕ) [NeZero q]
    (hΔ : Odd Δ) (hq : Odd q) (hsq : Squarefree q) :
    dualCorrelationLeadingTerm W M Δ K q =
      ((∫ x : ℝ in Ioi 0, W (x^2))/2) * ∑ b ∈ oddSquarefreeUpTo K,
        (Real.sqrt (M/b) : ℂ) * ((Nat.totient q : ℂ)/(q : ℂ)) *
          leadingDivisorCoefficient Δ q * (jacobiSym (b : ℤ) q : ℂ) := by
  unfold dualCorrelationLeadingTerm dualCorrelationFiniteForm
  have hterm (e : ℕ) (he : e ∈ (2*Δ).divisors) (s : ℤ) (hsm : s ∈ signedSquarefreeMultipliers)
      (b : ℕ) :
      dualCorrelationGaussFactor M e q * (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ) *
        dualSquareLeading W M e s b q =
      (μ e : ℂ) * ((M/(e*q) : ℝ) : ℂ) *
        gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
        (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ) * (1/2 : ℂ) *
        ((Nat.totient q : ℂ)/(q : ℂ)) * (Real.sqrt ((e : ℝ)*q/(M*b)) : ℂ) *
        ((1-(Real.sign (s : ℝ) : ℂ)*Complex.I)/(Real.sqrt |(s : ℝ)| : ℂ)) *
        (∫ x : ℝ in Ioi 0, W (x^2)) := by
    rw [dualCorrelationGaussFactor_eq, dualSquareLeading,
      dualSignedSquareWeight_eq W s (signedSquarefreeMultiplier_ne_zero hsm),
      dualSquare_integral W hc hs]
    ring
  rw [Finset.sum_congr rfl (fun e he => Finset.sum_congr rfl (fun s hsm =>
    Finset.sum_congr rfl (fun b hb => hterm e he s hsm b)))]
  rw [Finset.sum_congr rfl (fun e he => Finset.sum_comm), Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [dualPoisson_leading_term Δ q b hΔ hq hsq (mem_oddSquarefreeUpTo.mp hb).1 M hM]
  push_cast
  ring

end Ostmann.QuadraticSieve

end OAI
