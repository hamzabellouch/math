import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLogFourierBound
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWeightedGaussBound

namespace OAI

/-! # The literal Poisson weight in dyadic divisor sums -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

noncomputable def quadraticSmoothDivisor (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (N d : ℕ) (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
    (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      a s * conj (b t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ) *
        ρ (X / ((s : ℝ) * t))

noncomputable def quadraticSmoothGaussDivisor (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (N d : ℕ) (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
    (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      a s * conj (b t) * quadraticGaussMultiplier (s * t) *
      (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ) * ρ (X / ((s : ℝ) * t))

 theorem quadratic_smooth_divisor_eq (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    {N : ℕ} (hN : 0 < N) (d : ℕ) (a b : ℕ → ℂ) (m : ℤ)
    (ha : ∀ n < N, a n = 0) (hb : ∀ n < N, b n = 0) :
    quadraticSmoothDivisor ρ X N d a b m =
      quadraticLogWeightedDivisor (quadraticLogKernel ρ X N) (2 * N) (2 * N) d a b m := by
  unfold quadraticSmoothDivisor quadraticLogWeightedDivisor
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hsa : a s = 0
  · simp [hsa]
  by_cases htb : b t = 0
  · simp [htb]
  have hslo : N ≤ s := by
    by_contra hh
    exact hsa (ha s (by omega))
  have htlo : N ≤ t := by
    by_contra hh
    exact htb (hb t (by omega))
  have hshi := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
  have hthi := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).2
  rw [quadratic_log_kernel_identity ρ X hN hslo hshi htlo hthi]

 theorem quadratic_smooth_gauss_divisor_eq (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    {N : ℕ} (hN : 0 < N) (d : ℕ) (a b : ℕ → ℂ) (m : ℤ)
    (ha : ∀ n < N, a n = 0) (hb : ∀ n < N, b n = 0) :
    quadraticSmoothGaussDivisor ρ X N d a b m =
      quadraticLogWeightedGaussDivisor (quadraticLogKernel ρ X N) (2 * N) (2 * N) d a b m := by
  unfold quadraticSmoothGaussDivisor quadraticLogWeightedGaussDivisor
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hsa : a s = 0
  · simp [hsa]
  by_cases htb : b t = 0
  · simp [htb]
  have hslo : N ≤ s := by
    by_contra hh
    exact hsa (ha s (by omega))
  have htlo : N ≤ t := by
    by_contra hh
    exact htb (hb t (by omega))
  have hshi := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
  have hthi := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).2
  rw [quadratic_log_kernel_identity ρ X hN hslo hshi htlo hthi]

 theorem quadratic_smooth_divisor_bound (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M N D : ℕ) (X : ℝ), 0 < N → 0 < X →
      ∀ (a b : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ), 0 ≤ T →
      (∀ n < N, a n = 0) → (∀ n < N, b n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i) →
      (∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ i) (K₁ i)) →
      (∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ j) (K₂ j)) →
      (∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
        D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
        Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) a) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) b) ≤ T) →
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticSmoothDivisor ρ X N d a b m‖) ≤
          C * min 1 (((N : ℝ) ^ 2 / X) ^ A) *
            ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
  obtain ⟨C, hC, hc⟩ := quadratic_log_kernel_fourier_bound ρ A
  refine ⟨C, hC, ?_⟩
  intro M N D X hN hX a b K₁ K₂ T hT ha hb hK₁ hK₂ h₁ h₂ hcost
  have hcomp := quadratic_weighted_bilinear_bound (quadraticLogKernel ρ X N)
    M (2 * N) (2 * N) D a b K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hcost
  simp_rw [← quadratic_smooth_divisor_eq ρ X hN _ a b _ ha hb] at hcomp
  calc
    _ ≤ (∫ u : ℝ, ‖𝓕 (quadraticLogKernel ρ X N) u‖) *
        ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
      simpa only [pow_two, Nat.cast_add, Nat.cast_one] using hcomp
    _ ≤ (C * min 1 (((N : ℝ) ^ 2 / X) ^ A)) *
        ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
      gcongr
      exact hc X hX N hN
    _ = _ := by ring

 theorem quadratic_smooth_gauss_divisor_bound (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M N D : ℕ) (X : ℝ), 0 < N → 0 < X →
      ∀ (a b : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ), 0 ≤ T →
      (∀ n < N, a n = 0) → (∀ n < N, b n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i) →
      (∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ i) (K₁ i)) →
      (∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ j) (K₂ j)) →
      (∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
        D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
        Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) a) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) b) ≤ T) →
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticSmoothGaussDivisor ρ X N d a b m‖) ≤
          C * min 1 (((N : ℝ) ^ 2 / X) ^ A) *
            ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
  obtain ⟨C, hC, hc⟩ := quadratic_log_kernel_fourier_bound ρ A
  refine ⟨3 * C, by positivity, ?_⟩
  intro M N D X hN hX a b K₁ K₂ T hT ha hb hK₁ hK₂ h₁ h₂ hcost
  have hcomp := quadratic_weighted_gauss_bound (quadraticLogKernel ρ X N)
    M (2 * N) (2 * N) D a b K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hcost
  simp_rw [← quadratic_smooth_gauss_divisor_eq ρ X hN _ a b _ ha hb] at hcomp
  calc
    _ ≤ 3 * (∫ u : ℝ, ‖𝓕 (quadraticLogKernel ρ X N) u‖) *
        ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
      simpa only [pow_two, Nat.cast_add, Nat.cast_one] using hcomp
    _ ≤ 3 * (C * min 1 (((N : ℝ) ^ 2 / X) ^ A)) *
        ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
      gcongr
      exact hc X hX N hN
    _ = _ := by ring

end Ostmann

end OAI
