import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCoprimeJacobiPoisson
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallPairTransform

namespace OAI

/-! # The finite odd smoothing sum equals its original first Poisson transform -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_integer_weight_finite {M : ℕ} (hM : 0 < M) (F : ℤ → ℂ) :
    (∑' m : ℤ, F m * quadraticSieveWeight ((m : ℝ) / M)) =
      ∑ m ∈ Finset.Icc 1 (3 * M), F m * quadraticSieveWeight ((m : ℝ) / M) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    _ = ∑ m ∈ Finset.Icc (1 : ℤ) (3 * M),
        F m * quadraticSieveWeight ((m : ℝ) / M) := by
      apply tsum_eq_sum
      intro m hm
      have hz : quadraticSieveWeight ((m : ℝ) / M) = 0 := by
        by_cases hlo : m ≤ 0
        · apply quadraticSieveWeight_eq_zero (Or.inl ?_)
          have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast hlo
          exact (div_nonpos_of_nonpos_of_nonneg hmR hMR.le).trans (by norm_num)
        · have hhi : (3 * M : ℤ) < m := by
            simp only [Finset.mem_Icc] at hm
            omega
          apply quadraticSieveWeight_eq_zero (Or.inr ?_)
          apply (le_div_iff₀ hMR).mpr
          have hh : (3 : ℝ) * M < m := by exact_mod_cast hhi
          nlinarith
      rw [hz, mul_zero]
    _ = _ := by
      apply Finset.sum_bij (fun m _ => m.toNat)
      · intro m hm
        have hh := Finset.mem_Icc.mp hm
        apply Finset.mem_Icc.mpr
        constructor
        · omega
        · omega
      · intro m hm n hn he
        have hm₀ : 0 ≤ m := by have := (Finset.mem_Icc.mp hm).1; omega
        have hn₀ : 0 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
        omega
      · intro m hm
        refine ⟨(m : ℤ), ?_, by simp⟩
        have hh := Finset.mem_Icc.mp hm
        apply Finset.mem_Icc.mpr
        constructor <;> exact_mod_cast (by omega : _)
      · intro m hm
        have hm₀ : 0 ≤ m := by have := (Finset.mem_Icc.mp hm).1; omega
        have he : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm₀
        have hr : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast he
        rw [he, hr]

theorem quadratic_odd_kernel_poisson {M D q : ℕ} (hM : 0 < M) [NeZero D] [NeZero q]
    (hq : Squarefree q) (ho : Odd q) :
    (∑ m ∈ quadraticOddRange (3 * M), quadraticSieveWeight ((m : ℝ) / M) *
      (if (m : ℤ).gcd D = 1 then (1 : ℂ) else 0) * (jacobiSym m q : ℂ)) =
    quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
      (ArithmeticFunction.moebius e : ℂ) *
        (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        ∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
          𝓕 quadraticSieveWeight ((h : ℝ) * M / ((e : ℝ) * q)) := by
  have hD : 2 * D ≠ 0 := mul_ne_zero (by decide) (NeZero.ne D)
  have : NeZero (2 * D) := ⟨hD⟩
  rw [← quadratic_coprime_jacobi_poisson hq ho quadraticSieveWeight
    (show (0 : ℝ) < M by exact_mod_cast hM),
    quadratic_integer_weight_finite hM]
  unfold quadraticOddRange
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Int.cast_natCast]
  rw [quadratic_odd_coprime_mask]
  have hg : ((m : ℤ).gcd D = 1) ↔ m.Coprime D := by
    simp only [Int.gcd, Int.natAbs_natCast]
  simp only [hg]
  by_cases hm : Odd m
  · rw [ite_eq_left hm, ite_eq_left hm]
    ring
  · rw [ite_eq_right hm, ite_eq_right hm]
    ring

end Ostmann

end OAI
