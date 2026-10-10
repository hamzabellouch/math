import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrectionRowsBasic

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate MeasureTheory
open scoped SchwartzMap ArithmeticFunction.Moebius

noncomputable def dualZeroDivisorRows (W : 𝓢(ℝ, ℂ)) (M : ℝ) (N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (e : ℕ) (s : ℤ) (b : ℕ) (X₂ : ℕ → ℕ → ℝ) : ℂ :=
  (-(1/2 : ℂ) * ((M/e : ℝ) : ℂ) * (μ e : ℂ) * dualSignedSquareWeight W s 0) *
    ∑ d ∈ Finset.Icc 1 (N^2), (if (d : ℝ) ≤ X₂ e b then (μ d : ℂ) else 0) *
      gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) ((e : ℤ)*s) d (b : ℤ)

noncomputable def dualLargeDivisorRows (W : 𝓢(ℝ, ℂ)) (M : ℝ) (N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (e : ℕ) (s : ℤ) (b : ℕ) (X₂ : ℕ → ℕ → ℝ) : ℂ :=
  (-(1/2 : ℂ) * (μ e : ℂ) * (Real.sqrt (M/((e : ℝ)*b)) : ℂ) *
    (∫ x : ℝ, dualSignedSquareWeight W s x)) *
    ∑ d ∈ Finset.Icc 1 (N^2), (if X₂ e b < (d : ℝ) then (μ d : ℂ)/(d : ℂ) else 0) *
      gaussProductDivisorJacobiRow S S (sqrtCoefficients a)
        (sqrtCoefficients (fun n => conj (a n))) ((e : ℤ)*s) d (b : ℤ)

theorem dualZeroCorrection_pair_eq_rows (W : 𝓢(ℝ, ℂ)) (M : ℝ) (N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (e : ℕ) (s : ℤ) (b : ℕ) (X₂ : ℕ → ℕ → ℝ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    complementaryPair S a (fun q => dualCorrelationGaussFactor M e q *
      (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ) * dualSquareZeroCorrection W q s (X₂ e b)) =
      dualZeroDivisorRows W M N S a e s b X₂ := by
  let Z : ℂ := -(1/2 : ℂ) * ((M/e : ℝ) : ℂ) * (μ e : ℂ) * dualSignedSquareWeight W s 0
  have hfun (q : ℕ) : dualCorrelationGaussFactor M e q *
      (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ) * dualSquareZeroCorrection W q s (X₂ e b) =
      Z * (jacobiGaussRatio q * (jacobiSym (((e : ℤ)*s)*(b : ℤ)) q : ℂ) *
        ∑ d ∈ q.divisors, if (d : ℝ) ≤ X₂ e b then (μ d : ℂ) else 0) := by
    simp only [dualCorrelationGaussFactor, dualSquareZeroCorrection, Finset.sum_filter, Z]
    ring
  simp_rw [hfun]
  rw [complementaryPair_mul, gaussPair_divisor_exchange S a N b ((e : ℤ)*s) _ hS]
  rfl

theorem dualLargeCorrection_pair_eq_rows (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) (N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (e : ℕ) (s : ℤ) (b : ℕ) (he : 0 < e) (hb : 0 < b)
    (X₂ : ℕ → ℕ → ℝ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    complementaryPair S a (fun q => dualCorrelationGaussFactor M e q *
      (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ) * dualSquareLargeCorrection W M e s b q (X₂ e b)) =
      dualLargeDivisorRows W M N S a e s b X₂ := by
  let Z : ℂ := -(1/2 : ℂ) * (μ e : ℂ) * (Real.sqrt (M/((e : ℝ)*b)) : ℂ) *
    (∫ x : ℝ, dualSignedSquareWeight W s x)
  let F : ℕ → ℂ := fun d => if X₂ e b < (d : ℝ) then (μ d : ℂ)/(d : ℂ) else 0
  have hfun (q : ℕ) : dualCorrelationGaussFactor M e q *
      (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ) * dualSquareLargeCorrection W M e s b q (X₂ e b) =
      Z * ((Real.sqrt (q : ℝ) : ℂ) * jacobiGaussRatio q *
        (jacobiSym (((e : ℤ)*s)*(b : ℤ)) q : ℂ) * ∑ d ∈ q.divisors, F d) := by
    have hscale : ((M/e : ℝ) : ℂ) * (Real.sqrt ((e : ℝ)*q/(M*b)) : ℂ) =
        (Real.sqrt (M/((e : ℝ)*b)) : ℂ) * (Real.sqrt (q : ℝ) : ℂ) := by
      exact_mod_cast dual_correction_root_scale (e := (e : ℝ)) (b := (b : ℝ)) hM (by exact_mod_cast he)
        (by exact_mod_cast hb) (Nat.cast_nonneg q)
    simp only [dualCorrelationGaussFactor, dualSquareLargeCorrection, Finset.sum_filter, Z, F]
    linear_combination (-(1/2 : ℂ)*(μ e : ℂ)*jacobiGaussRatio q*
      (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ)*(∫ x : ℝ, dualSignedSquareWeight W s x)*
      (∑ d ∈ q.divisors, if X₂ e b < (d : ℝ) then (μ d : ℂ)/(d : ℂ) else 0)) * hscale
  simp_rw [hfun]
  rw [complementaryPair_mul, rootGaussPair_divisor_exchange S a N b ((e : ℤ)*s) _ hS]
  change Z * _ = Z * _
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [← Finset.sum_mul]
  rw [sum_rootGaussMellinKernel]
  dsimp only [F]
  ring

theorem dualCorrelationZeroCorrection_eq_rows (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₂ : ℕ → ℕ → ℝ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    dualCorrelationZeroCorrection W M Δ K S a X₂ =
      ∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers, ∑ b ∈ oddSquarefreeUpTo K,
        dualZeroDivisorRows W M N S a e s b X₂ := by
  unfold dualCorrelationZeroCorrection dualCorrelationZeroTerm dualCorrelationFiniteForm
  simp_rw [complementaryPair_sum]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro b hb
  exact dualZeroCorrection_pair_eq_rows W M N S a e s b X₂ hS

theorem dualCorrelationLargeCorrection_eq_rows (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) (Δ K N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₂ : ℕ → ℕ → ℝ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    dualCorrelationLargeCorrection W M Δ K S a X₂ =
      ∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers, ∑ b ∈ oddSquarefreeUpTo K,
        dualLargeDivisorRows W M N S a e s b X₂ := by
  unfold dualCorrelationLargeCorrection dualCorrelationLargeTerm dualCorrelationFiniteForm
  simp_rw [complementaryPair_sum]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro b hb
  exact dualLargeCorrection_pair_eq_rows W M hM N S a e s b (Nat.pos_of_mem_divisors he)
    (mem_oddSquarefreeUpTo.mp hb).1 X₂ hS

end Ostmann.QuadraticSieve

end OAI
