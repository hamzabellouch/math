import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter

structure KernelFactorization (z : ℤ) where
  kernel : ℤ
  squareFactor : ℕ
  squareFactor_pos : 0 < squareFactor
  kernel_squarefree : Squarefree kernel
  factorization : z = kernel * (squareFactor : ℤ) ^ 2

theorem exists_kernelFactorization {z : ℤ} (hz : z ≠ 0) :
    Nonempty (KernelFactorization z) := by
  obtain ⟨t, u, h, hu⟩ := exists_sq_mul_squarefree z
  have ht : t ≠ 0 := by
    intro ht
    simp [ht] at h
    exact hz h.symm
  refine ⟨⟨u, t.natAbs, Int.natAbs_pos.mpr ht, hu, ?_⟩⟩
  simpa [Int.natCast_natAbs, sq_abs, mul_comm] using h.symm

noncomputable def kernelFactorization (z : ℤ) (hz : z ≠ 0) : KernelFactorization z :=
  Classical.choice (exists_kernelFactorization hz)

namespace KernelFactorization
variable {z : ℤ} (F : KernelFactorization z)

theorem kernel_ne_zero : F.kernel ≠ 0 := F.kernel_squarefree.ne_zero

theorem kernel_dvd : F.kernel ∣ z := ⟨_, F.factorization⟩

theorem abs_factorization : z.natAbs = F.kernel.natAbs * F.squareFactor ^ 2 := by
  simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using
    congrArg Int.natAbs F.factorization

theorem kernel_abs_le : F.kernel.natAbs ≤ z.natAbs := by
  rw [F.abs_factorization]
  exact Nat.le_mul_of_pos_right _ (pow_pos F.squareFactor_pos _)

theorem kernel_isCoprime {m h x : ℤ} (hc : IsCoprime h m)
    (heq : z = m * x - h) : IsCoprime F.kernel m := by
  have hz : IsCoprime z m := by simpa [heq] using hc
  exact hz.of_isCoprime_of_dvd_left F.kernel_dvd

theorem squareFactor_isCoprime {m h x : ℤ} (hc : IsCoprime h m)
    (heq : z = m * x - h) : IsCoprime (F.squareFactor : ℤ) m := by
  have hz : IsCoprime z m := by simpa [heq] using hc
  apply hz.of_isCoprime_of_dvd_left
  refine ⟨F.kernel * F.squareFactor, ?_⟩
  calc
    z = F.kernel * (F.squareFactor : ℤ) ^ 2 := F.factorization
    _ = (F.squareFactor : ℤ) * (F.kernel * F.squareFactor) := by ring

end KernelFactorization
end Ostmann.QuadraticCenter

end OAI
