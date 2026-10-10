import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticKernelSeparation

namespace OAI

/-! # Disjoint prime supports identify a kernel pair from its product -/

namespace Ostmann

open scoped Classical

theorem cross_coprime_factor_unique {a b c d : ℕ} (ha : 0 < a)
    (had : a.Coprime d) (hcb : c.Coprime b) (hprod : a * b = c * d) :
    a = c ∧ b = d := by
  have hac : a ∣ c := had.dvd_of_dvd_mul_right (hprod ▸ dvd_mul_right a b)
  have hca : c ∣ a := hcb.dvd_of_dvd_mul_right (hprod.symm ▸ dvd_mul_right c d)
  have hacEq := Nat.dvd_antisymm hac hca
  refine ⟨hacEq, ?_⟩
  rw [← hacEq] at hprod
  exact Nat.eq_of_mul_eq_mul_left ha hprod

theorem signed_kernel_product_magnitudes {u v u' v' : ℤ} (hu : u ≠ 0)
    (huv' : u.natAbs.Coprime v'.natAbs) (hu'v : u'.natAbs.Coprime v.natAbs)
    (hprod : u * v = u' * v') : u.natAbs = u'.natAbs ∧ v.natAbs = v'.natAbs := by
  apply cross_coprime_factor_unique (Int.natAbs_pos.mpr hu) huv' hu'v
  simpa only [Int.natAbs_mul] using congrArg Int.natAbs hprod

/-- For any fixed signed product there are at most two pairs from two
nonzero kernel families with disjoint prime supports. -/
theorem kernel_product_fiber_card_le_two (A B : Finset ℤ) (d : ℤ)
    (hA : ∀ u ∈ A, u ≠ 0)
    (hAB : ∀ u ∈ A, ∀ v ∈ B, u.natAbs.Coprime v.natAbs) :
    Fintype.card {z : A × B // (z.1 : ℤ) * (z.2 : ℤ) = d} ≤ 2 := by
  let F := {z : A × B // (z.1 : ℤ) * (z.2 : ℤ) = d}
  let sign : F → Bool := fun z => decide (0 ≤ (z.1.1 : ℤ))
  have hinj : Function.Injective sign := by
    intro z w hsign
    have hu := hA z.1.1 z.1.1.property
    have hprod : (z.1.1 : ℤ) * (z.1.2 : ℤ) = (w.1.1 : ℤ) * (w.1.2 : ℤ) :=
      z.2.trans w.2.symm
    have habs := (signed_kernel_product_magnitudes hu
      (hAB z.1.1 z.1.1.property w.1.2 w.1.2.property)
      (hAB w.1.1 w.1.1.property z.1.2 z.1.2.property) hprod).1
    have heq : (z.1.1 : ℤ) = (w.1.1 : ℤ) := by
      by_cases hz : 0 ≤ (z.1.1 : ℤ) <;> by_cases hw : 0 ≤ (w.1.1 : ℤ)
      · exact (Int.natAbs_inj_of_nonneg_of_nonneg hz hw).mp habs
      · simp [sign, hz, hw] at hsign
      · simp [sign, hz, hw] at hsign
      · exact (Int.natAbs_inj_of_nonpos_of_nonpos (le_of_not_ge hz) (le_of_not_ge hw)).mp habs
    have heq' : (z.1.2 : ℤ) = (w.1.2 : ℤ) := by
      rw [← heq] at hprod
      exact mul_left_cancel₀ hu hprod
    apply Subtype.ext
    exact Prod.ext (Subtype.ext heq) (Subtype.ext heq')
  exact (Fintype.card_le_of_injective sign hinj).trans_eq Fintype.card_bool

end Ostmann

end OAI
