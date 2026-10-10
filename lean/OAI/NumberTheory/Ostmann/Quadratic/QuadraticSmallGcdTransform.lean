import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRoughGcdDescent
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRoughSecondAssembly

namespace OAI

/-! # The actual small-gcd moment in the Poisson comparison -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_rough_gcd_pair_sum (M N K D : ℕ) (v : ℕ → ℂ) :
    quadraticRoughGcdMoment M N K D v =
      ∑ z ∈ quadraticGcdPairs N D, v z.1 * conj (v z.2) *
        ∑ m ∈ quadraticRoughKernelRange (3 * M) K,
          quadraticSieveWeight ((m : ℝ) / M) * (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ) := by
  unfold quadraticRoughGcdMoment quadraticGcdKernelSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro m _
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have hj := congrArg (fun x : ℤ => (x : ℂ))
    (jacobi_pair_kernel (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2 (m : ℤ))
  rw [hg] at hj
  push_cast at hj
  calc
    _ = (v z.1 * conj (v z.2)) * quadraticSieveWeight ((m : ℝ) / M) *
        ((jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ)) := by
      rw [hj]
      split_ifs <;> ring
    _ = _ := by ring

theorem quadratic_rough_gcd_transform {M : ℕ} (hM : 0 < M)
    (N K D : ℕ) (v : ℕ → ℂ) :
    quadraticRoughGcdMoment M N K D v =
      ∑ z ∈ quadraticGcdPairs N D, v z.1 * conj (v z.2) *
        (quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2) -
          quadraticSmallPairSum M K D (quadraticPairKernel z.1 z.2)) := by
  rw [quadratic_rough_gcd_pair_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [quadratic_rough_pair_transform hM K hz]

/-- Small gcds cannot contain a diagonal pair in the actual dyadic support. -/
theorem quadratic_small_gcd_ne_diagonal {R D : ℕ} (hDR : D < R)
    (v : ℕ → ℂ) (hsupp : ∀ n ∈ oddSquarefreeRange (2 * R), n < R → v n = 0)
    {z : ℕ × ℕ} (hz : z ∈ quadraticGcdPairs (2 * R) D) (hv : v z.1 ≠ 0) :
    z.1 ≠ z.2 := by
  intro heq
  have hg := (Finset.mem_filter.mp hz).2
  rw [heq, Nat.gcd_self] at hg
  have hs := (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
  apply hv
  apply hsupp z.1 hs
  omega

noncomputable def quadraticGcdMomentCorrections (M R K D : ℕ) (J : ℝ)
    (v : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (v z.2) *
    (quadraticFirstSecondCorrections M D (quadraticPairKernel z.1 z.2) K ((R : ℝ) / D) J -
      ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
        (jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
          quadraticSmallPairCorrection M J (2 * (quadraticPairKernel z.1 z.2 * D)) b)

noncomputable def quadraticGcdMomentError (M R K D : ℕ) (J : ℝ) (v : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (v z.2) *
    ((quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2) -
      quadraticFirstKernelFinite M D (quadraticPairKernel z.1 z.2) K) +
     (quadraticFirstKernelFinite M D (quadraticPairKernel z.1 z.2) K -
      quadraticFirstSecondKernel M D (quadraticPairKernel z.1 z.2) K ((R : ℝ) / D) J) -
     (quadraticSmallPairSum M K D (quadraticPairKernel z.1 z.2) -
      quadraticSmallPairCore M K D (quadraticPairKernel z.1 z.2) J))

theorem quadratic_small_gcd_moment_decomposition {M : ℕ} (hM : 0 < M)
    (R K D : ℕ) (J : ℝ) (v : ℕ → ℂ) :
    quadraticRoughGcdMoment M (2 * R) K D v =
      (quadraticTransformedFirstMain M (2 * R) D K quadraticSieveWeight v -
        quadraticSmallTransformedMain M (2 * R) D K quadraticSieveWeight v) +
      quadraticGcdMomentCorrections M R K D J v + quadraticGcdMomentError M R K D J v := by
  rw [quadratic_rough_gcd_transform hM,
    ← quadratic_pair_main_difference_sum]
  unfold quadraticGcdMomentCorrections quadraticGcdMomentError
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [quadratic_first_second_kernel_split, quadratic_small_pair_core_main]
  unfold quadraticPairMainDifference
  ring

end Ostmann

end OAI
