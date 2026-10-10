import OAI.GroupTheory.PolycyclicRecognition.Analysis.NoetherianIntegralTorsion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteIntegerReductions

namespace OAI

/-! # Finite integral torsion from noetherianity and finite prime reductions -/

noncomputable section
namespace PolycyclicRecognition
open scoped nonZeroDivisors
variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherian R M]

theorem finite_integral_torsion_of_finite_reductions
    (h : ∀ p : ℕ, p.Prime → Finite (M ⧸ integerMultiples M p)) :
    Finite (Submodule.torsion' R M ℤ⁰) := by
  obtain ⟨z, hz, hkill⟩ := noetherian_integral_torsion_exponent R M
  let n := z.natAbs
  have hn : n ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have hk (x : M) (hx : x ∈ Submodule.torsion' R M ℤ⁰) : (n : ℤ) • x = 0 := by
    change (z.natAbs : ℤ) • x = 0
    rw [Int.natCast_natAbs]
    by_cases hpos : 0 ≤ z
    · rw [abs_of_nonneg hpos]
      exact hkill x hx
    · rw [abs_of_neg (lt_of_not_ge hpos), neg_smul, hkill x hx, neg_zero]
  let := finite_integerReduction_of_primes M h n hn
  let T := Submodule.torsion' R M ℤ⁰
  let F : T → M ⧸ integerMultiples M n := fun x => (integerMultiples M n).mkQ x
  apply Finite.of_injective F
  intro x y hxy
  have hd : (x : M) - (y : M) ∈ integerMultiples M n :=
    (Submodule.Quotient.eq _).mp hxy
  obtain ⟨a, ha⟩ := (mem_integerMultiples M n _).mp hd
  have ha0 : ((n : ℤ) * n) • a = 0 := by
    rw [mul_smul, ha]
    exact hk _ (T.sub_mem x.property y.property)
  have haT : a ∈ T := by
    refine ⟨⟨(n : ℤ) * n, mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero hnZ hnZ)⟩, ?_⟩
    exact ha0
  apply Subtype.ext
  apply sub_eq_zero.mp
  exact ha.symm.trans (hk a haT)

end PolycyclicRecognition

end

end OAI
