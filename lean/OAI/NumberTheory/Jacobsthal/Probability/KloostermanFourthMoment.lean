import OAI.NumberTheory.Jacobsthal.Estimates.PairCollisionCount

namespace OAI

namespace Erdos970

section

open scoped BigOperators ComplexConjugate

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

variable {F : Type*} [Field F] [Fintype F]

private theorem fourth_expand (ψ : AddChar F ℂ) (a b : F) :
    sum ψ a b * sum ψ a b * conj (sum ψ a b) * conj (sum ψ a b) =
    ∑ x : (Fˣ × Fˣ) × (Fˣ × Fˣ), ψ
      (a * ((x.2.1 : F) + x.2.2 - x.1.1 - x.1.2) +
       b * ((↑x.2.1⁻¹ : F) + ↑x.2.2⁻¹ - ↑x.1.1⁻¹ - ↑x.1.2⁻¹)) := by
  simp only [sum, map_sum, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_neg_eq_conj,
    ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem two_frequency_orthogonality (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (x y : F) :
    (∑ a : F, ∑ b : F, ψ (a*x + b*y)) =
      if x = 0 ∧ y = 0 then (Fintype.card F : ℂ)^2 else 0 := by
  simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_sum,
    AddChar.sum_mulShift _ hψ, ← Finset.sum_mul, AddChar.sum_mulShift _ hψ]
  split_ifs <;> simp_all [pow_two]

theorem fourth_moment_identity (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ a : F, ∑ b : F,
      sum ψ a b * sum ψ a b * conj (sum ψ a b) * conj (sum ψ a b)) =
    (Fintype.card F : ℂ)^2 * (pairCollisions F).card := by
  simp_rw [fourth_expand]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [two_frequency_orthogonality ψ hψ]
  have heq (x : (Fˣ × Fˣ) × (Fˣ × Fˣ)) :
      ((x.2.1 : F) + x.2.2 - x.1.1 - x.1.2 = 0 ∧
        (↑x.2.1⁻¹ : F) + ↑x.2.2⁻¹ - ↑x.1.1⁻¹ - ↑x.1.2⁻¹ = 0) ↔
      ((x.1.1 : F) + x.1.2 = x.2.1 + x.2.2 ∧
        (↑x.1.1⁻¹ : F) + ↑x.1.2⁻¹ = ↑x.2.1⁻¹ + ↑x.2.2⁻¹) := by
    simp only [sub_sub, sub_eq_zero, eq_comm]
  simp_rw [heq]
  rw [← Finset.sum_filter]
  simp only [pairCollisions, Finset.sum_const, nsmul_eq_mul]
  ring

end ErdosKloosterman

end

end Erdos970

end OAI
