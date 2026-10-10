import Mathlib.Data.Nat.Totient
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdReduction
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernelCharacter

namespace OAI

/-! # The exact totient-weighted kernel after removal of the common divisor -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticTotientKernelSum (N D : ℕ) (b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs N D, b z.1 * conj (b z.2) *
    ((Nat.totient (quadraticPairKernel z.1 z.2) : ℂ) / quadraticPairKernel z.1 z.2) *
    (jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ)

noncomputable def quadraticTotientCoeff (D s : ℕ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  if D.Coprime n ∧ s.Coprime n then (Nat.totient n : ℂ) / n * b (D * n) else 0

 theorem quadratic_totient_kernel_reduction {N D : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (b : ℕ → ℂ) (s : ℕ) (r : ℤ) :
    quadraticTotientKernelSum N D b ((s : ℤ) ^ 2 * r) =
      quadraticGcdKernelSum (N / D) 1 (quadraticTotientCoeff D s b) r := by
  unfold quadraticTotientKernelSum
  have hr := quadratic_gcd_pair_reindex (N := N) hD hDo (fun a c =>
    b a * conj (b c) * ((Nat.totient (quadraticPairKernel a c) : ℂ) / quadraticPairKernel a c) *
      (jacobiSym ((s : ℤ) ^ 2 * r) (quadraticPairKernel a c) : ℂ))
  rw [hr]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hz
  have hsa := (Finset.mem_filter.mp ha).2.2
  have hsb := (Finset.mem_filter.mp hb).2.2
  have hab : z.1.Coprime z.2 := hg
  have hk : quadraticPairKernel z.1 z.2 = z.1 * z.2 := by
    simp only [quadraticPairKernel, hg, Nat.div_one]
  rw [quadraticPairKernel_mul_coprime hD.ne_zero hab, hk,
    jacobi_square_mul s r (mul_ne_zero hsa.ne_zero hsb.ne_zero)]
  have ht : ((z.1 * z.2).totient : ℂ) / (z.1 * z.2 : ℕ) =
      ((z.1.totient : ℂ) / z.1) * ((z.2.totient : ℂ) / z.2) := by
    rw [Nat.totient_mul hab]
    push_cast
    exact div_mul_div_comm _ _ _ _ |>.symm
  rw [ht]
  by_cases hDa : D.Coprime z.1 <;> by_cases hDb : D.Coprime z.2 <;>
    by_cases hta : s.Coprime z.1 <;> by_cases htb : s.Coprime z.2 <;>
    simp [quadraticTotientCoeff, hDa, hDb, hta, htb, Nat.coprime_mul_iff_right,
      mul_assoc, mul_left_comm, mul_comm]
  rw [ite_eq_left (And.intro hDa hDb), ite_eq_left (And.intro hta htb),
    ite_eq_left (And.intro hDa hta), ite_eq_left (And.intro hDb htb)]
  simp only [map_mul, map_div₀, map_natCast]
  ring

 theorem quadraticTotientCoeff_norm_le (D s : ℕ) (b : ℕ → ℂ) (n : ℕ) :
    ‖quadraticTotientCoeff D s b n‖ ≤ ‖b (D * n)‖ := by
  unfold quadraticTotientCoeff
  split_ifs
  · rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    have hratio : (n.totient : ℝ) / n ≤ 1 := by
      by_cases hn : n = 0
      · simp [hn]
      · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr
          (by exact_mod_cast Nat.totient_le n)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
  · simp

 theorem quadraticTotientCoeff_energy_le {D N : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (s : ℕ) (b : ℕ → ℂ) :
    quadraticSieveEnergy (N / D) (quadraticTotientCoeff D s b) ≤ quadraticSieveEnergy N b := by
  have hh : quadraticSieveEnergy (N / D) (quadraticTotientCoeff D s b) ≤
      quadraticSieveEnergy (N / D) (quadraticDivisibilityCoeff D b) := by
    apply Finset.sum_le_sum
    intro n _
    by_cases hc : D.Coprime n
    · rw [quadraticDivisibilityCoeff, ite_eq_left hc]
      have hn := quadraticTotientCoeff_norm_le D s b n
      exact
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
    · simp [quadraticTotientCoeff, quadraticDivisibilityCoeff, hc]
  apply hh.trans
  rw [quadraticSieveEnergy_divisibility D N hD hDo]
  apply Finset.sum_le_sum
  intro n _
  dsimp only
  split_ifs <;> simp

end Ostmann

end OAI
