import OAI.NumberTheory.Ostmann.Quadratic.QuadraticEnergyExponent

namespace OAI

/-! # A finite dyadic decomposition of the large squarefree kernels -/

namespace Ostmann

open scoped BigOperators

def dyadicKernelShell (s : ℕ) : ℕ := Nat.log 2 (s - 1)

theorem dyadicKernelShell_mem (s : ℕ) (hs : 2 ≤ s) :
    s ∈ Finset.Ioc (2 ^ dyadicKernelShell s) (2 * 2 ^ dyadicKernelShell s) := by
  have hlo := Nat.pow_log_le_self 2 (show s - 1 ≠ 0 by omega)
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (s - 1)
  rw [pow_succ] at hhi
  exact Finset.mem_Ioc.mpr ⟨by dsimp [dyadicKernelShell]; omega,
    by dsimp [dyadicKernelShell]; omega⟩

theorem dyadicKernelShell_le (s M : ℕ) (hs : s ≤ M) :
    dyadicKernelShell s ≤ Nat.log 2 M :=
  Nat.log_mono_right ((Nat.sub_le s 1).trans hs)

theorem dyadicKernelShell_modulus (L s : ℕ) (hs : 4 * L ^ 2 ≤ s) (hs2 : 2 ≤ s) :
    2 * L ^ 2 ≤ 2 ^ dyadicKernelShell s := by
  have hh := (Finset.mem_Ioc.mp (dyadicKernelShell_mem s hs2)).2
  omega

theorem sum_dyadicKernelShells (S : Finset ℕ) (M : ℕ) (hS : ∀ s ∈ S, s ≤ M)
    (f : ℕ → ℝ) :
    (∑ s ∈ S, f s) = ∑ j ∈ Finset.range (Nat.log 2 M + 1),
      ∑ s ∈ S.filter (fun s => dyadicKernelShell s = j), f s := by
  classical
  exact (Finset.sum_fiberwise_of_maps_to
    (fun s hs => Finset.mem_range.mpr (Nat.lt_succ_of_le (dyadicKernelShell_le s M (hS s hs)))) f).symm

end Ostmann

end OAI
