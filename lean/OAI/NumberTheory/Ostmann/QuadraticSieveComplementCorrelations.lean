import OAI.NumberTheory.Ostmann.QuadraticSieveComplementCorrelationsBasic

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate MeasureTheory Set
open scoped SchwartzMap FourierTransform ArithmeticFunction.Moebius

noncomputable def complementLargeKernel (X₂ : ℕ → ℝ) (v d : ℕ) : ℂ :=
  if X₂ v < (d : ℝ) then (1 : ℂ) / d else 0

noncomputable def complementFourierKernel (W : 𝓢(ℝ, ℂ)) (M : ℝ)
    (X₁ X₂ L : ℕ → ℝ) (v d : ℕ) : ℂ :=
  if X₁ v < (d : ℝ) ∧ (d : ℝ) ≤ X₂ v then
    ((Real.sqrt (M/v) / d : ℝ) : ℂ) * ∑ l ∈ nonzeroIntegerCutoff (L v),
      𝓕 (squarePullback W 1 (by norm_num)) ((l : ℝ) * (Real.sqrt (M/v) / d)) else 0

noncomputable def complementaryLargeCorrection (M : ℝ) (I : ℂ) (K Δ N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₂ : ℕ → ℝ) : ℂ :=
  -I * ∑ v ∈ oddSquarefreeUpTo K, if Nat.Coprime v Δ then
    (Real.sqrt (M/v) : ℂ) * ∑ r ∈ (2*Δ).divisors, ∑ d ∈ Finset.Icc 1 (N^2),
      (μ r : ℂ) * (μ d : ℂ) * complementLargeKernel X₂ v (r*d) *
        coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v : ℤ) else 0

noncomputable def complementaryFourierCorrection (W : 𝓢(ℝ, ℂ)) (M : ℝ) (K Δ N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₁ X₂ L : ℕ → ℝ) : ℂ :=
  (1/2 : ℂ) * ∑ v ∈ oddSquarefreeUpTo K, if Nat.Coprime v Δ then
    ∑ r ∈ (2*Δ).divisors, ∑ d ∈ Finset.Icc 1 (N^2),
      (μ r : ℂ) * (μ d : ℂ) * complementFourierKernel W M X₁ X₂ L v (r*d) *
        coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v : ℤ) else 0

theorem complementaryPoissonMain_components (W : 𝓢(ℝ, ℂ))
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) (M : ℝ) (K Δ q : ℕ) (X₁ X₂ L : ℕ → ℝ) :
    complementaryPoissonMain W M K Δ q X₁ X₂ L =
      ∑ v ∈ oddSquarefreeUpTo K, if Nat.Coprime v Δ then
        (∫ x : ℝ in Ioi 0, W (x^2)) * (Real.sqrt (M/v) : ℂ) *
          ((Nat.totient (2*q*Δ) : ℂ) / (2*q*Δ : ℕ)) * (jacobiSym (v : ℤ) q : ℂ)
        - ((∫ x : ℝ in Ioi 0, W (x^2)) * (Real.sqrt (M/v) : ℂ)) *
          ((jacobiSym (v : ℤ) q : ℂ) * ∑ d ∈ (2*q*Δ).divisors,
            (μ d : ℂ) * complementLargeKernel X₂ v d)
        + (1/2 : ℂ) * ((jacobiSym (v : ℤ) q : ℂ) * ∑ d ∈ (2*q*Δ).divisors,
            (μ d : ℂ) * complementFourierKernel W M X₁ X₂ L v d) else 0 := by
  classical
  rw [complementaryPoissonMain, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hc : Nat.Coprime v Δ
  · rw [ite_eq_left hc, ite_eq_left hc, coprimePoissonMain_square W hs]
    have hlarge : (∑ d ∈ (2*q*Δ).divisors.filter (fun d : ℕ => X₂ v < (d : ℝ)),
        (μ d : ℂ) / d) =
        ∑ d ∈ (2*q*Δ).divisors, (μ d : ℂ) * complementLargeKernel X₂ v d := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      unfold complementLargeKernel
      split_ifs <;> ring
    have hfourier : (∑ d ∈ (2*q*Δ).divisors.filter
        (fun d : ℕ => X₁ v < (d : ℝ) ∧ (d : ℝ) ≤ X₂ v),
        (μ d : ℂ) * ((Real.sqrt (M/v) / d : ℝ) : ℂ) *
          ∑ l ∈ nonzeroIntegerCutoff (L v),
            𝓕 (squarePullback W 1 (by norm_num)) ((l : ℝ) * (Real.sqrt (M/v) / d))) =
        ∑ d ∈ (2*q*Δ).divisors, (μ d : ℂ) * complementFourierKernel W M X₁ X₂ L v d := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      unfold complementFourierKernel
      split_ifs <;> ring
    rw [hlarge, hfourier]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc, mul_zero]

theorem complementaryCorrelationMain_eq (W : 𝓢(ℝ, ℂ))
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) (M : ℝ) (K Δ N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₁ X₂ L : ℕ → ℝ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ Nat.Coprime (2*Δ) n) :
    complementaryCorrelationMain W M K Δ S a X₁ X₂ L =
      complementLeadingCorrelation M (∫ x : ℝ in Ioi 0, W (x^2)) K Δ S a +
        complementaryLargeCorrection M (∫ x : ℝ in Ioi 0, W (x^2)) K Δ N S a X₂ +
        complementaryFourierCorrection W M K Δ N S a X₁ X₂ L := by
  classical
  let I : ℂ := ∫ x : ℝ in Ioi 0, W (x^2)
  rw [complementaryCorrelationMain]
  simp_rw [complementaryPoissonMain_components W hs]
  rw [complementaryPair_sum]
  simp_rw [complementaryPair_ite]
  have heq (v : ℕ) :
      (if Nat.Coprime v Δ then complementaryPair S a (fun q =>
        I * (Real.sqrt (M/v) : ℂ) * ((Nat.totient (2*q*Δ) : ℂ) / (2*q*Δ : ℕ)) *
          (jacobiSym (v : ℤ) q : ℂ)
        - (I * (Real.sqrt (M/v) : ℂ)) * ((jacobiSym (v : ℤ) q : ℂ) *
          ∑ d ∈ (2*q*Δ).divisors, (μ d : ℂ) * complementLargeKernel X₂ v d)
        + (1/2 : ℂ) * ((jacobiSym (v : ℤ) q : ℂ) *
          ∑ d ∈ (2*q*Δ).divisors, (μ d : ℂ) * complementFourierKernel W M X₁ X₂ L v d)) else 0) =
      (if Nat.Coprime v Δ then complementaryPair S a (fun q =>
        I * (Real.sqrt (M/v) : ℂ) * ((Nat.totient (2*q*Δ) : ℂ) / (2*q*Δ : ℕ)) *
          (jacobiSym (v : ℤ) q : ℂ)) else 0)
      - I * (if Nat.Coprime v Δ then (Real.sqrt (M/v) : ℂ) *
        ∑ r ∈ (2*Δ).divisors, ∑ d ∈ Finset.Icc 1 (N^2),
          (μ r : ℂ) * (μ d : ℂ) * complementLargeKernel X₂ v (r*d) *
            coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v : ℤ) else 0)
      + (1/2 : ℂ) * (if Nat.Coprime v Δ then
        ∑ r ∈ (2*Δ).divisors, ∑ d ∈ Finset.Icc 1 (N^2),
          (μ r : ℂ) * (μ d : ℂ) * complementFourierKernel W M X₁ X₂ L v (r*d) *
            coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v : ℤ) else 0) := by
    by_cases hc : Nat.Coprime v Δ
    · simp only [ite_eq_left hc]
      rw [complementaryPair_add, complementaryPair_sub,
        complementaryPair_mul, complementaryPair_mul,
        complementaryPair_divisors S a N Δ v _ hS,
        complementaryPair_divisors S a N Δ v _ hS]
      ring
    · simp only [ite_eq_right hc, mul_zero, sub_self, zero_add]
  rw [Finset.sum_congr rfl (fun v hv => heq v)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [complementaryPair_leading]
  simp only [complementaryLargeCorrection, complementaryFourierCorrection]
  dsimp only [I]
  ring

theorem complementaryCorrelationMain_eq_of_oddSquarefree (W : 𝓢(ℝ, ℂ))
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) (M : ℝ) (K Δ N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₁ X₂ L : ℕ → ℝ)
    (hS : S ⊆ oddSquarefreeUpTo N) (hc : ∀ n ∈ S, Nat.Coprime n Δ) :
    complementaryCorrelationMain W M K Δ S a X₁ X₂ L =
      complementLeadingCorrelation M (∫ x : ℝ in Ioi 0, W (x^2)) K Δ S a +
        complementaryLargeCorrection M (∫ x : ℝ in Ioi 0, W (x^2)) K Δ N S a X₂ +
        complementaryFourierCorrection W M K Δ N S a X₁ X₂ L := by
  apply complementaryCorrelationMain_eq W hs M K Δ N S a X₁ X₂ L
  intro n hn
  obtain ⟨hp, hb, ho, hsq⟩ := mem_oddSquarefreeUpTo.mp (hS hn)
  exact ⟨hp, hb, (Nat.coprime_two_left.mpr ho).mul_left (hc n hn).symm⟩

end Ostmann.QuadraticSieve

end OAI
