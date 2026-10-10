import OAI.Geometry.EinsteinFour.HeatDriftTransportAlgebra

namespace OAI

/-! Contraction of the twice-differentiated pullback. The Jacobian
derivative cancels exactly against the transformed density drift. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem heat_trace_pullback_algebra (J a H Q : Mat4) (hH : J * a * Jᵀ = H) :
    (∑ i, ∑ j, a i j * (∑ r, ∑ s, J r i * J s j * Q r s)) =
      ∑ r, ∑ s, H r s * Q r s := by
  have he (i j : Fin 4) : (∑ r, ∑ s, J r i * J s j * Q r s) =
      (weightedConnection J (fun r => Matrix.of (fun _ s => Q r s)) i * J) 0 j := by
    simp only [weightedConnection, Matrix.mul_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp_rw [he]
  exact heat_weighted_connection_trace J a H (fun r => Matrix.of (fun _ s => Q r s)) hH 0

theorem heat_rough_trace_algebra (J a H Q : Mat4)
    (P : Fin 4 → Mat4) (b S B : Fin 4 → ℝ)
    (hH : J * a * Jᵀ = H)
    (hP : ∀ i j r, P j r i = P i r j)
    (hb : ∀ r, (∑ i, J r i * b i) - (∑ i, ∑ j, a i j * P i r j) = B r) :
    -(∑ i, ∑ j, a i j *
      ((∑ r, P j r i * S r) + (∑ r, ∑ s, J r i * J s j * Q r s))) +
      (∑ i, b i * (∑ r, J r i * S r)) =
        -(∑ r, ∑ s, H r s * Q r s) + ∑ r, B r * S r := by
  have hp : (∑ i, ∑ j, a i j * (∑ r, P j r i * S r)) =
      ∑ r, (∑ i, ∑ j, a i j * P j r i) * S r := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  have hq : (∑ i, b i * (∑ r, J r i * S r)) =
      ∑ r, (∑ i, J r i * b i) * S r := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hb' (r : Fin 4) : (∑ i, J r i * b i) -
      (∑ i, ∑ j, a i j * P j r i) = B r := by
    have he : (∑ i, ∑ j, a i j * P j r i) = ∑ i, ∑ j, a i j * P i r j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hP i j r]
    rw [he]
    exact hb r
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hp, hq, heat_trace_pullback_algebra J a H Q hH]
  have h : (∑ r, (∑ i, J r i * b i) * S r) -
      (∑ r, (∑ i, ∑ j, a i j * P j r i) * S r) = ∑ r, B r * S r := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [← sub_mul, hb']
  linarith only [h]

end
end PositiveEinsteinFour.Geometry

end OAI
