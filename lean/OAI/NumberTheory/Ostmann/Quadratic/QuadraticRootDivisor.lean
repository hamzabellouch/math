import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLogRootKernel
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticVaryingGauss

namespace OAI

/-! # The literal square-root weights in the second Poisson comparison -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

noncomputable def quadraticRootDivisor (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (N d : ℕ) (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
    (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      a s * conj (b t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ) *
        ρ (X * Real.sqrt ((s : ℝ) * t))

noncomputable def quadraticRootGaussDivisor (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (N d : ℕ) (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
    (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      a s * conj (b t) * quadraticGaussMultiplier (s * t) *
      (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ) * ρ (X * Real.sqrt ((s : ℝ) * t))

 theorem quadratic_root_divisor_eq (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    {N : ℕ} (hN : 0 < N) (d : ℕ) (a b : ℕ → ℂ) (m : ℤ)
    (ha : ∀ n < N, a n = 0) (hb : ∀ n < N, b n = 0) :
    quadraticRootDivisor ρ X N d a b m =
      quadraticLogWeightedDivisor (quadraticLogRootKernel ρ X N) (2 * N) (2 * N) d a b m := by
  unfold quadraticRootDivisor quadraticLogWeightedDivisor
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
  rw [quadratic_log_root_kernel_identity ρ X hN hslo hshi htlo hthi]

 theorem quadratic_root_gauss_divisor_eq (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    {N : ℕ} (hN : 0 < N) (d : ℕ) (a b : ℕ → ℂ) (m : ℤ)
    (ha : ∀ n < N, a n = 0) (hb : ∀ n < N, b n = 0) :
    quadraticRootGaussDivisor ρ X N d a b m =
      quadraticLogWeightedGaussDivisor (quadraticLogRootKernel ρ X N) (2 * N) (2 * N) d a b m := by
  unfold quadraticRootGaussDivisor quadraticLogWeightedGaussDivisor
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
  rw [quadratic_log_root_kernel_identity ρ X hN hslo hshi htlo hthi]

 theorem quadratic_varying_root_bound (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M N D : ℕ) (X : ℕ → ℕ → ℝ) (Y : ℝ), 0 < N → 0 < Y →
      (∀ d ∈ Finset.Ioc D (2 * D), ∀ m ∈ oddSquarefreeRange M, Y ≤ X d m) →
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
        ‖quadraticRootDivisor ρ (X d m) N d a b m‖) ≤
          C * min 1 (1 / (Y * N) ^ A) *
            ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
  obtain ⟨C, hC, hc⟩ := quadratic_log_root_kernel_envelope ρ A
  let J := ∫ u : ℝ, quadraticFourierEnvelope u
  have hJ : 0 ≤ J := integral_nonneg quadraticFourierEnvelope_nonneg
  refine ⟨C * J, by positivity, ?_⟩
  intro M N D X Y hN hY hYX a b K₁ K₂ T hT ha hb hK₁ hK₂ h₁ h₂ hcost
  let Z := min 1 (1 / (Y * N) ^ A)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let f : ℕ → ℕ → 𝓢(ℝ, ℂ) := fun d m => quadraticLogRootKernel ρ (X d m) N
  let ω := fun u : ℝ => (C * Z) * quadraticFourierEnvelope u
  have hω : Integrable ω := quadraticFourierEnvelope_integrable.const_mul _
  have hω₀ : ∀ u, 0 ≤ ω u := fun u => mul_nonneg (mul_nonneg hC hZ)
    (quadraticFourierEnvelope_nonneg u)
  have hf : ∀ d ∈ Finset.Ioc D (2 * D), ∀ m ∈ oddSquarefreeRange M,
      ∀ u : ℝ, ‖𝓕 (f d m) u‖ ≤ ω u := by
    intro d hd m hm u
    exact hc N hN (X d m) Y hY (hYX d hd m hm) u
  have hcomp := quadratic_varying_weighted_bilinear_bound f ω hω hω₀
    M (2 * N) (2 * N) D a b K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hf hcost
  have he : (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticRootDivisor ρ (X d m) N d a b m‖) =
      ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticLogWeightedDivisor (f d m) (2 * N) (2 * N) d a b m‖ := by
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro m _
    rw [quadratic_root_divisor_eq ρ (X d m) hN d a b m ha hb]
  rw [he]
  calc
    _ ≤ (∫ u : ℝ, ω u) *
        ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
      simpa only [pow_two, Nat.cast_add, Nat.cast_one] using hcomp
    _ = _ := by
      dsimp only [ω, J]
      rw [integral_const_mul]
      ring

 theorem quadratic_varying_root_gauss_bound (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M N D : ℕ) (X : ℕ → ℕ → ℝ) (Y : ℝ), 0 < N → 0 < Y →
      (∀ d ∈ Finset.Ioc D (2 * D), ∀ m ∈ oddSquarefreeRange M, Y ≤ X d m) →
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
        ‖quadraticRootGaussDivisor ρ (X d m) N d a b m‖) ≤
          C * min 1 (1 / (Y * N) ^ A) *
            ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
  obtain ⟨C, hC, hc⟩ := quadratic_log_root_kernel_envelope ρ A
  let J := ∫ u : ℝ, quadraticFourierEnvelope u
  have hJ : 0 ≤ J := integral_nonneg quadraticFourierEnvelope_nonneg
  refine ⟨3 * C * J, by positivity, ?_⟩
  intro M N D X Y hN hY hYX a b K₁ K₂ T hT ha hb hK₁ hK₂ h₁ h₂ hcost
  let Z := min 1 (1 / (Y * N) ^ A)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let f : ℕ → ℕ → 𝓢(ℝ, ℂ) := fun d m => quadraticLogRootKernel ρ (X d m) N
  let ω := fun u : ℝ => (C * Z) * quadraticFourierEnvelope u
  have hω : Integrable ω := quadraticFourierEnvelope_integrable.const_mul _
  have hω₀ : ∀ u, 0 ≤ ω u := fun u => mul_nonneg (mul_nonneg hC hZ)
    (quadraticFourierEnvelope_nonneg u)
  have hf : ∀ d ∈ Finset.Ioc D (2 * D), ∀ m ∈ oddSquarefreeRange M,
      ∀ u : ℝ, ‖𝓕 (f d m) u‖ ≤ ω u := by
    intro d hd m hm u
    exact hc N hN (X d m) Y hY (hYX d hd m hm) u
  have hcomp := quadratic_varying_weighted_gauss_bound f ω hω hω₀
    M (2 * N) (2 * N) D a b K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hf hcost
  have he : (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticRootGaussDivisor ρ (X d m) N d a b m‖) =
      ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticLogWeightedGaussDivisor (f d m) (2 * N) (2 * N) d a b m‖ := by
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro m _
    rw [quadratic_root_gauss_divisor_eq ρ (X d m) hN d a b m ha hb]
  rw [he]
  calc
    _ ≤ 3 * (∫ u : ℝ, ω u) *
        ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
      simpa only [pow_two, Nat.cast_add, Nat.cast_one] using hcomp
    _ = _ := by
      dsimp only [ω, J]
      rw [integral_const_mul]
      ring

end Ostmann

end OAI
