import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOddWeightPoisson
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallMomentError

namespace OAI

/-! # The exact first transform of the full smoothed moment -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate FourierTransform

noncomputable def quadraticFirstKernelTransform (M D q : ℕ) : ℂ :=
  quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
    (ArithmeticFunction.moebius e : ℂ) *
      (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
      ∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
        𝓕 quadraticSieveWeight ((h : ℝ) * M / ((e : ℝ) * q))

noncomputable def quadraticFirstMomentTransform (M N : ℕ) (v : ℕ → ℂ) : ℂ :=
  ∑ D ∈ Finset.Icc 1 N, ∑ z ∈ quadraticGcdPairs N D,
    v z.1 * conj (v z.2) * quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2)

theorem quadratic_first_moment_transform {M : ℕ} (hM : 0 < M) (N : ℕ) (v : ℕ → ℂ) :
    (quadraticSmoothEnergy M N v : ℂ) = quadraticFirstMomentTransform M N v := by
  rw [quadratic_smooth_energy_gcd]
  unfold quadraticFirstMomentTransform
  apply Finset.sum_congr rfl
  intro D hD
  have : NeZero D := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hD).1⟩
  simp only [quadraticGcdKernelSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have hq := quadraticPairKernel_squarefree (Finset.mem_filter.mp hs).2.2
    (Finset.mem_filter.mp ht).2.2
  have ho := quadraticPairKernel_odd (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp ht).2.1
  have : NeZero (quadraticPairKernel z.1 z.2) := ⟨hq.ne_zero⟩
  calc
    _ = v z.1 * conj (v z.2) *
        ∑ m ∈ quadraticOddRange (3 * M), quadraticSieveWeight ((m : ℝ) / M) *
          (if (m : ℤ).gcd D = 1 then (1 : ℂ) else 0) *
            (jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = _ := by rw [quadratic_odd_kernel_poisson hM hq ho]; rfl

theorem quadratic_rough_moment_error (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ, 0 < M → ∀ J : ℝ, 1 ≤ J → ∀ v : ℕ → ℂ,
      ‖(quadraticRoughEnergy M N K v : ℂ) -
        (quadraticFirstMomentTransform M N v - quadraticSmallMomentCore M N K J v)‖ ≤
      (C * Real.sqrt M * K / J ^ A) * N * quadraticSieveEnergy N v := by
  obtain ⟨C, hC, hc⟩ := quadratic_small_moment_error A
  refine ⟨C, hC, ?_⟩
  intro M N K hM J hJ v
  have he := congrArg (fun x : ℝ => (x : ℂ)) (quadratic_smooth_energy_split M N K v)
  rw [Complex.ofReal_add, quadratic_first_moment_transform hM] at he
  have hid : (quadraticRoughEnergy M N K v : ℂ) -
      (quadraticFirstMomentTransform M N v - quadraticSmallMomentCore M N K J v) =
      -((quadraticSmallEnergy M N K v : ℂ) - quadraticSmallMomentCore M N K J v) := by
    rw [he]
    ring
  rw [hid, norm_neg]
  exact hc M N K hM J hJ v

end Ostmann

end OAI
