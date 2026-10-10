import OAI.NumberTheory.Jacobsthal.Estimates.PairCollisionCount

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosKloosterman.PrimePower

variable {R : Type*} [CommRing R] [Fintype R]

attribute [local instance] Classical.decEq

noncomputable def stationaryUnits (q a b : R) : Finset Rˣ :=
  Finset.univ.filter fun u => q * (a - b * (↑u⁻¹ : R)^2) = 0

private theorem sum_shift (ψ : AddChar R ℂ) (a b q : R) (hq : q^2 = 0) (z : R) :
    sum ψ a b = ∑ u : Rˣ,
      ψ (a * (u : R) + b * (↑u⁻¹ : R)) *
        ψ (z * (q * (a - b * (↑u⁻¹ : R)^2))) := by
  have ht : (q*z)^2 = 0 := by rw [mul_pow, hq, zero_mul]
  have he := Equiv.sum_comp (shiftEquiv (q*z) ht)
    (fun u : Rˣ => ψ (a * (u : R) + b * (↑u⁻¹ : R)))
  unfold sum
  rw [← he]
  apply Finset.sum_congr rfl
  intro u _
  change ψ (a * (shiftUnit u (q*z) ht : R) +
    b * (↑(shiftUnit u (q*z) ht)⁻¹ : R)) = _
  rw [phase_shift, AddChar.map_add_eq_mul]
  congr 1
  congr 1
  ring

theorem stationary_phase_identity (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (a b q : R) (hq : q^2 = 0) :
    sum ψ a b = ∑ u ∈ stationaryUnits q a b,
      ψ (a * (u : R) + b * (↑u⁻¹ : R)) := by
  have hcard : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  calc
    (Fintype.card R : ℂ) * sum ψ a b = ∑ _z : R, sum ψ a b := by simp
    _ = ∑ z : R, ∑ u : Rˣ,
        ψ (a * (u : R) + b * (↑u⁻¹ : R)) *
          ψ (z * (q * (a - b * (↑u⁻¹ : R)^2))) := by
      apply Finset.sum_congr rfl
      intro z _
      exact sum_shift ψ a b q hq z
    _ = ∑ u : Rˣ, ψ (a * (u : R) + b * (↑u⁻¹ : R)) *
        (∑ z : R, ψ (z * (q * (a - b * (↑u⁻¹ : R)^2)))) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = _ := by
      simp_rw [AddChar.sum_mulShift _ hψ]
      rw [Finset.mul_sum]
      simp [stationaryUnits, Finset.sum_filter, mul_comm]

theorem norm_sum_le_stationary_card (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (a b q : R) (hq : q^2 = 0) :
    ‖sum ψ a b‖ ≤ (stationaryUnits q a b).card := by
  rw [stationary_phase_identity ψ hψ a b q hq]
  calc
    _ ≤ ∑ u ∈ stationaryUnits q a b, ‖ψ (a * (u : R) + b * (↑u⁻¹ : R))‖ :=
      norm_sum_le _ _
    _ = _ := by simp [AddChar.norm_apply]

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
