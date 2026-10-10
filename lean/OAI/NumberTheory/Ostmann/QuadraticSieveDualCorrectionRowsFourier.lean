import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrectionRows

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped SchwartzMap FourierTransform ArithmeticFunction.Moebius

noncomputable def dualFourierDivisorRows (W : 𝓢(ℝ, ℂ)) (M : ℝ) (N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (e : ℕ) (s : ℤ) (b : ℕ)
    (X₁ X₂ L : ℕ → ℕ → ℝ) : ℂ :=
  ((1/2 : ℂ) * (μ e : ℂ) * (Real.sqrt (M/((e : ℝ)*b)) : ℂ)) *
    ∑ d ∈ Finset.Icc 1 (N^2),
      (if X₁ e b < (d : ℝ) ∧ (d : ℝ) ≤ X₂ e b then (μ d : ℂ)/(d : ℂ) else 0) *
      ∑ l ∈ nonzeroIntegerCutoff (L e b), ∑ n ∈ S, ∑ t ∈ S,
        rootGaussMellinKernel a (fun n => conj (a n)) ((e : ℤ)*s) d b n t *
          𝓕 (dualSignedSquareWeight W s)
            (((l : ℝ)*Real.sqrt ((e : ℝ)/M))*Real.sqrt ((n : ℝ)*t)/((d : ℝ)*Real.sqrt b))

theorem dualFourierCorrection_pair_eq_rows (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) (N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (e : ℕ) (s : ℤ) (b : ℕ) (he : 0 < e) (hb : 0 < b)
    (X₁ X₂ L : ℕ → ℕ → ℝ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    complementaryPair S a (fun q => dualCorrelationGaussFactor M e q *
      (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ) *
        dualSquareFourierCorrection W M e s b q (X₁ e b) (X₂ e b) (L e b)) =
      dualFourierDivisorRows W M N S a e s b X₁ X₂ L := by
  let Z : ℂ := (1/2 : ℂ) * (μ e : ℂ) * (Real.sqrt (M/((e : ℝ)*b)) : ℂ)
  let H : ℕ → ℂ := fun d =>
    if X₁ e b < (d : ℝ) ∧ (d : ℝ) ≤ X₂ e b then (μ d : ℂ)/(d : ℂ) else 0
  let F : ℕ → ℕ → ℂ := fun d q => H d * ∑ l ∈ nonzeroIntegerCutoff (L e b),
    𝓕 (dualSignedSquareWeight W s)
      (((l : ℝ)*Real.sqrt ((e : ℝ)/M))*Real.sqrt (q : ℝ)/((d : ℝ)*Real.sqrt b))
  have hep : (0 : ℝ) < e := by exact_mod_cast he
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  have hfun (q : ℕ) : dualCorrelationGaussFactor M e q *
      (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ) *
        dualSquareFourierCorrection W M e s b q (X₁ e b) (X₂ e b) (L e b) =
      Z * ((Real.sqrt (q : ℝ) : ℂ) * jacobiGaussRatio q *
        (jacobiSym (((e : ℤ)*s)*(b : ℤ)) q : ℂ) * ∑ d ∈ q.divisors, F d q) := by
    have hscale : ((M/e : ℝ) : ℂ) * (Real.sqrt ((e : ℝ)*q/(M*b)) : ℂ) =
        (Real.sqrt (M/((e : ℝ)*b)) : ℂ) * (Real.sqrt (q : ℝ) : ℂ) := by
      exact_mod_cast dual_correction_root_scale hM hep hbp (Nat.cast_nonneg q)
    simp only [dualCorrelationGaussFactor, dualSquareFourierCorrection, Finset.sum_filter,
      Finset.mul_sum, Z, F]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hcut : X₁ e b < (d : ℝ) ∧ (d : ℝ) ≤ X₂ e b
    · simp only [H, ite_eq_left hcut]
      simp_rw [dual_correction_fourier_scale hM hep hbp (Nat.cast_nonneg q)]
      simp_rw [← Finset.mul_sum]
      push_cast at hscale ⊢
      linear_combination ((1/2 : ℂ)*(μ e : ℂ)*jacobiGaussRatio q*
        (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ)*((μ d : ℂ)/(d : ℂ))*
        (∑ l ∈ nonzeroIntegerCutoff (L e b), 𝓕 (dualSignedSquareWeight W s)
          (((l : ℝ)*Real.sqrt ((e : ℝ)/M))*Real.sqrt (q : ℝ)/((d : ℝ)*Real.sqrt b)))) * hscale
    · simp only [H, ite_eq_right hcut, mul_zero, zero_mul, Finset.sum_const_zero]
  simp_rw [hfun]
  rw [complementaryPair_mul, rootGaussPair_divisor_exchange S a N b ((e : ℤ)*s) _ hS]
  change Z * _ = Z * _
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  simp only [F, Nat.cast_mul, Finset.mul_sum]
  calc
    _ = ∑ n ∈ S, ∑ l ∈ nonzeroIntegerCutoff (L e b), ∑ t ∈ S,
        H d * (rootGaussMellinKernel a (fun n => conj (a n)) ((e : ℤ)*s) d b n t *
          𝓕 (dualSignedSquareWeight W s)
            (((l : ℝ)*Real.sqrt ((e : ℝ)/M))*Real.sqrt ((n : ℝ)*t)/((d : ℝ)*Real.sqrt b))) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = _ := Finset.sum_comm

theorem dualCorrelationFourierCorrection_eq_rows (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) (Δ K N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₁ X₂ L : ℕ → ℕ → ℝ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    dualCorrelationFourierCorrection W M Δ K S a X₁ X₂ L =
      ∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers, ∑ b ∈ oddSquarefreeUpTo K,
        dualFourierDivisorRows W M N S a e s b X₁ X₂ L := by
  unfold dualCorrelationFourierCorrection dualCorrelationFourierTerm dualCorrelationFiniteForm
  simp_rw [complementaryPair_sum]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro b hb
  exact dualFourierCorrection_pair_eq_rows W M hM N S a e s b (Nat.pos_of_mem_divisors he)
    (mem_oddSquarefreeUpTo.mp hb).1 X₁ X₂ L hS

end Ostmann.QuadraticSieve

end OAI
