import OAI.Geometry.EinsteinFour.ConnectionPullback

namespace OAI

/-! Finite contractions in the coordinate transformation of the drift. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem heat_inverse_congruence_component (J a : Mat4) (p q : Fin 4) :
    (∑ i, ∑ j, J p i * a i j * J q j) = (J * a * Jᵀ) p q := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem heat_weighted_connection_trace (J a H : Mat4) (D : Fin 4 → Mat4)
    (hH : J * a * Jᵀ = H) (r : Fin 4) :
    (∑ i, ∑ j, a i j * (weightedConnection J D i * J) r j) =
      ∑ p, ∑ q, H p q * D p r q := by
  have he (i j : Fin 4) : a i j * (weightedConnection J D i * J) r j =
      ∑ p, ∑ q, (J p i * a i j * J q j) * D p r q := by
    simp only [weightedConnection, Matrix.mul_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [he]
  calc
    _ = ∑ p, ∑ q, ∑ i, ∑ j, (J p i * a i j * J q j) * D p r q := by
      conv_lhs =>
        arg 2
        ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      conv_lhs =>
        arg 2
        ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      simp_rw [← Finset.sum_mul]
      rw [heat_inverse_congruence_component, hH]

theorem heat_drift_transport_algebra (J a H : Mat4) (C P D : Fin 4 → Mat4)
    (hC : ∀ i, J * C i = P i + weightedConnection J D i * J)
    (hH : J * a * Jᵀ = H) (r : Fin 4) :
    (∑ k, J r k * (∑ i, ∑ j, a i j * C i k j)) -
      (∑ i, ∑ j, a i j * P i r j) = ∑ p, ∑ q, H p q * D p r q := by
  have he : (∑ k, J r k * (∑ i, ∑ j, a i j * C i k j)) =
      ∑ i, ∑ j, a i j * (J * C i) r j := by
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  simp_rw [hC, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  rw [add_sub_cancel_left]
  exact heat_weighted_connection_trace J a H D hH r

end
end PositiveEinsteinFour.Geometry

end OAI
