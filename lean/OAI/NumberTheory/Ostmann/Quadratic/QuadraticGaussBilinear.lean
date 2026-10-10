import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGaussMultiplier
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticBilinearComparison

namespace OAI

/-! # Separating the Gauss factor in the actual divisor bilinear sum -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticGaussLeft (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * quadraticGaussMultiplier n

noncomputable def quadraticGaussRight (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  b n * conj (quadraticGaussMultiplier n)

noncomputable def quadraticThreeClass (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n % 4 = 3 then a n else 0

noncomputable def quadraticGaussDivisorBilinear (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange N₁, ∑ t ∈ oddSquarefreeRange N₂,
    (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      a s * conj (b t) * quadraticGaussMultiplier (s * t) *
      (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)

 theorem quadratic_gauss_divisor_bilinear_split (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) :
    quadraticGaussDivisorBilinear N₁ N₂ d a b m =
      quadraticDivisorBilinear N₁ N₂ d (quadraticGaussLeft a) (quadraticGaussRight b) m -
      2 * quadraticDivisorBilinear N₁ N₂ d
        (quadraticThreeClass (quadraticGaussLeft a))
        (quadraticThreeClass (quadraticGaussRight b)) m := by
  unfold quadraticGaussDivisorBilinear quadraticDivisorBilinear
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨_, hos, hss⟩ := Finset.mem_filter.mp hs
  obtain ⟨_, hot, hst⟩ := Finset.mem_filter.mp ht
  by_cases hc : s.Coprime t ∧ d ∣ s * t
  · rw [ite_eq_left hc, quadraticGaussMultiplier_mul hc.1 hss hst hos hot]
    simp only [quadraticGaussLeft, quadraticGaussRight, quadraticThreeClass,
      map_mul, starRingEnd_self_apply]
    by_cases hs3 : s % 4 = 3 <;> by_cases ht3 : t % 4 = 3 <;>
      simp only [hs3, ht3, and_self, and_false, false_and, ite_true, ite_false,
        map_zero, map_mul, starRingEnd_self_apply, mul_zero, zero_mul, sub_zero, one_mul] <;> ring
  · simp [hc]

 theorem quadraticGaussLeft_norm {N n : ℕ} (hn : n ∈ oddSquarefreeRange N)
    (a : ℕ → ℂ) : ‖quadraticGaussLeft a n‖ = ‖a n‖ := by
  obtain ⟨_, ho, hs⟩ := Finset.mem_filter.mp hn
  rw [quadraticGaussLeft, norm_mul, quadraticGaussMultiplier_norm hs ho, mul_one]

 theorem quadraticGaussRight_norm {N n : ℕ} (hn : n ∈ oddSquarefreeRange N)
    (b : ℕ → ℂ) : ‖quadraticGaussRight b n‖ = ‖b n‖ := by
  obtain ⟨_, ho, hs⟩ := Finset.mem_filter.mp hn
  rw [quadraticGaussRight, norm_mul, Complex.norm_conj,
    quadraticGaussMultiplier_norm hs ho, mul_one]

 theorem quadraticSieveEnergy_gaussLeft (N : ℕ) (a : ℕ → ℂ) :
    quadraticSieveEnergy N (quadraticGaussLeft a) = quadraticSieveEnergy N a := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [quadraticGaussLeft_norm hn]

 theorem quadraticSieveEnergy_gaussRight (N : ℕ) (b : ℕ → ℂ) :
    quadraticSieveEnergy N (quadraticGaussRight b) = quadraticSieveEnergy N b := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [quadraticGaussRight_norm hn]

 theorem quadraticSieveEnergy_threeClass (N : ℕ) (a : ℕ → ℂ) :
    quadraticSieveEnergy N (quadraticThreeClass a) ≤ quadraticSieveEnergy N a := by
  apply Finset.sum_le_sum
  intro n _
  unfold quadraticThreeClass
  split_ifs
  · rfl
  · simp

 theorem quadraticDivisorMoment_gaussLeft (N : ℕ) (a : ℕ → ℂ) :
    quadraticDivisorMoment N (quadraticGaussLeft a) = quadraticDivisorMoment N a := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [quadraticGaussLeft_norm hn]

 theorem quadraticDivisorMoment_gaussRight (N : ℕ) (b : ℕ → ℂ) :
    quadraticDivisorMoment N (quadraticGaussRight b) = quadraticDivisorMoment N b := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [quadraticGaussRight_norm hn]

 theorem quadraticDivisorMoment_threeClass (N : ℕ) (a : ℕ → ℂ) :
    quadraticDivisorMoment N (quadraticThreeClass a) ≤ quadraticDivisorMoment N a := by
  apply Finset.sum_le_sum
  intro n _
  unfold quadraticThreeClass
  split_ifs
  · rfl
  · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    positivity

end Ostmann

end OAI
