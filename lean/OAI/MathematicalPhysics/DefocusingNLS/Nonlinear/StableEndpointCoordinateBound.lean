import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableCoordinateBackwardBound
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI

/-! # Small unstable coordinates of the actual decaying endpoint sequence -/

namespace DefocusingNLS

section Inverse
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem finiteCoordinate_rightInverse_leftInverse (D R : F →L[ℝ] F)
    (hDR : ∀ v, D (R v) = v) (v : F) : R (D v) = v := by
  have hsurj : Function.Surjective D := fun v => ⟨R v, hDR v⟩
  have hinj : Function.Injective D :=
    (D.toLinearMap.injective_iff_surjective).mpr hsurj
  apply hinj
  exact hDR (D v)
end Inverse

section Endpoint
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem stableEndpoint_coordinate_bound
    (π : ℕ → E →L[ℝ] F) (A : ℕ → E →L[ℝ] E) (D R : F →L[ℝ] F)
    (hRD : ∀ v, R (D v) = v) (hR : ‖R‖ ≤ 1)
    (C τ κ ε B r : ℝ)
    (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (hπ : ∀ n, ‖π n‖ ≤ C)
    (he : ∀ n, ‖(π (n + 1)).comp (A n) - D.comp (π n)‖ ≤ τ)
    (h : ℕ → E → E) (z : ℕ → E)
    (hstep : ∀ n, z (n + 1) = A n (z n) + h n (z n))
    (hz : ∀ n, ‖z n‖ ≤ B * (1 / 2 : ℝ) ^ n)
    (hh : ∀ n, ‖h n (z n) - h n 0‖ ≤ κ * ‖z n‖)
    (hzero : ∀ n, ‖h n 0‖ ≤ ε * r ^ n) :
    ‖π 0 (z 0)‖ ≤ 2 * ((τ + C * κ) * B + C * ε) := by
  let u : ℕ → F := fun n => π n (z n)
  let f : ℕ → F := fun n =>
    ((π (n + 1)).comp (A n) - D.comp (π n)) (z n) + π (n + 1) (h n (z n))
  have hrec (n : ℕ) : u n = R (u (n + 1) - f n) := by
    have hid : u (n + 1) - f n = D (u n) := by
      dsimp only [u, f]
      rw [hstep n, map_add]
      simp only [sub_apply, ContinuousLinearMap.comp_apply]
      abel
    rw [hid, hRD]
  have hf (n : ℕ) : ‖f n‖ ≤ ((τ + C * κ) * B + C * ε) * (1 / 2 : ℝ) ^ n := by
    have hhn : ‖h n (z n)‖ ≤ κ * (B * (1 / 2 : ℝ) ^ n) + ε * (1 / 2 : ℝ) ^ n := by
      calc
        _ = ‖(h n (z n) - h n 0) + h n 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖h n (z n) - h n 0‖ + ‖h n 0‖ := norm_add_le _ _
        _ ≤ κ * ‖z n‖ + ε * r ^ n := add_le_add (hh n) (hzero n)
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hz n) hκ)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrhalf n) hε)
    calc
      ‖f n‖ ≤ ‖((π (n + 1)).comp (A n) - D.comp (π n)) (z n)‖ +
          ‖π (n + 1) (h n (z n))‖ := norm_add_le _ _
      _ ≤ τ * ‖z n‖ + C * ‖h n (z n)‖ :=
        add_le_add (ContinuousLinearMap.le_of_opNorm_le _ (he n) _)
          (ContinuousLinearMap.le_of_opNorm_le _ (hπ (n + 1)) _)
      _ ≤ τ * (B * (1 / 2 : ℝ) ^ n) +
          C * (κ * (B * (1 / 2 : ℝ) ^ n) + ε * (1 / 2 : ℝ) ^ n) :=
        add_le_add (mul_le_mul_of_nonneg_left (hz n) hτ)
          (mul_le_mul_of_nonneg_left hhn hC)
      _ = _ := by ring
  apply stableCoordinate_initial_bound R hR u f (C * B)
    ((τ + C * κ) * B + C * ε) (by positivity) _ hf hrec
  intro n
  exact (ContinuousLinearMap.le_of_opNorm_le _ (hπ n) _).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hz n) hC)

end Endpoint
end DefocusingNLS

end OAI
