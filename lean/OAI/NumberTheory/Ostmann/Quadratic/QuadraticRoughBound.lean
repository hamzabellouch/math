import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmoothedEnergy
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdCoefficientBridge
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCoprimeEnergy

namespace OAI

/-! # Restriction and divisor descent for the actual rough moment -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

def QuadraticRoughBound (M N K : ℕ) (T : ℝ) : Prop :=
  ∀ v : ℕ → ℂ, quadraticRoughEnergy M N K v ≤ T * quadraticSieveEnergy N v

theorem QuadraticRoughBound.mono_constant {M N K : ℕ} {T U : ℝ}
    (h : QuadraticRoughBound M N K T) (hTU : T ≤ U) : QuadraticRoughBound M N K U := by
  intro v
  exact (h v).trans (mul_le_mul_of_nonneg_right hTU (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem quadraticRoughEnergy_restrict {N R : ℕ} (hNR : N ≤ R)
    (M K : ℕ) (v : ℕ → ℂ) :
    quadraticRoughEnergy M R K (fun n => if n ∈ oddSquarefreeRange N then v n else 0) =
      quadraticRoughEnergy M N K v := by
  unfold quadraticRoughEnergy quadraticTransposeSum
  apply Finset.sum_congr rfl
  intro m _
  congr 2
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (oddSquarefreeRange_mono hNR)]

theorem QuadraticRoughBound.mono_second {M N R K : ℕ} {T : ℝ}
    (hNR : N ≤ R) (h : QuadraticRoughBound M R K T) : QuadraticRoughBound M N K T := by
  intro v
  have hh := h (fun n => if n ∈ oddSquarefreeRange N then v n else 0)
  rwa [quadraticRoughEnergy_restrict hNR, quadraticSieveEnergy_restrict hNR] at hh

theorem quadratic_rough_divisibility {M N K d : ℕ} (hd : Squarefree d) (ho : Odd d)
    (v : ℕ → ℂ) :
    quadraticRoughEnergy M N K (fun n => if d ∣ n then v n else 0) ≤
      quadraticRoughEnergy M (N / d) K (quadraticDivisibilityCoeff d v) := by
  unfold quadraticRoughEnergy
  apply Finset.sum_le_sum
  intro m _
  apply mul_le_mul_of_nonneg_left _ (quadraticSieveBump_nonneg _)
  rw [quadraticTransposeSum_divisibility d N hd ho, norm_mul, mul_pow]
  have hn : ‖(jacobiSym (m : ℤ) d : ℂ)‖ ^ 2 ≤ 1 := by
    rcases jacobiSym.trichotomy (m : ℤ) d with h | h | h <;> simp [h]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (sq_nonneg _)

noncomputable def quadraticRoughGcdMoment (M N K D : ℕ) (v : ℕ → ℂ) : ℂ :=
  ∑ m ∈ quadraticRoughKernelRange (3 * M) K,
    quadraticSieveWeight ((m : ℝ) / M) *
      (if (m : ℤ).gcd D = 1 then (1 : ℂ) else 0) * quadraticGcdKernelSum N D v m

theorem quadratic_gcd_kernel_remove {N D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v : ℕ → ℂ) (m : ℤ) :
    quadraticGcdKernelSum N D v m =
      quadraticGcdKernelSum (N / D) 1 (quadraticDivisibilityCoeff D v) m := by
  unfold quadraticGcdKernelSum
  rw [quadratic_gcd_coefficient_reindex hD ho v v (fun q => (jacobiSym m q : ℂ))]
  apply Finset.sum_congr rfl
  intro z hz
  have hg := (Finset.mem_filter.mp hz).2
  simp only [quadraticPairKernel, hg, Nat.div_one]

/-- Removing the gcd and then the coprimality condition only introduces actual
rough moments of divisor-restricted coefficients. -/
theorem quadratic_rough_gcd_moment_divisors {M N K D : ℕ}
    (hD : Squarefree D) (ho : Odd D) (v : ℕ → ℂ) :
    ‖quadraticRoughGcdMoment M N K D v‖ ≤
      ∑ d ∈ Finset.Icc 1 (N / D), quadraticRoughEnergy M (N / D) K
        (fun n => if d ∣ n then quadraticDivisibilityCoeff D v n else 0) := by
  unfold quadraticRoughGcdMoment
  simp_rw [quadratic_gcd_kernel_remove hD ho,
    quadratic_coprime_energy_expansion, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ m ∈ quadraticRoughKernelRange (3 * M) K, ∑ d ∈ Finset.Icc 1 (N / D),
        quadraticSieveBump ((m : ℝ) / M) *
          ‖quadraticTransposeSum (N / D)
            (fun n => if d ∣ n then quadraticDivisibilityCoeff D v n else 0) m‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro m _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d _
      have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hw : ‖quadraticSieveWeight ((m : ℝ) / M)‖ = quadraticSieveBump ((m : ℝ) / M) := by
        rw [quadraticSieveWeight_apply, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (quadraticSieveBump_nonneg _)]
      by_cases hc : (m : ℤ).gcd D = 1
      · simp only [ite_eq_left hc, norm_mul, mul_one, norm_pow,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hw]
        simpa only [one_mul] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖quadraticTransposeSum (N / D)
            (fun n => if d ∣ n then quadraticDivisibilityCoeff D v n else 0) m‖))
          (quadraticSieveBump_nonneg ((m : ℝ) / M))
      · simp only [ite_eq_right hc, mul_zero, zero_mul, norm_zero]
        exact mul_nonneg (quadraticSieveBump_nonneg _) (sq_nonneg _)
    _ = _ := by rw [Finset.sum_comm]; rfl

end Ostmann

end OAI
