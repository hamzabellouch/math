import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombQuadrature

namespace OAI

/-! Polynomial mesh and precision budgets for the six-coordinate
Coulomb quadrature. All varying parameters below are unary naturals. -/

noncomputable section
namespace ContinuumCoulomb.CoulombQuadratureSchedule

def volume (R : ℕ) : ℕ := (2 * R) ^ 6
def lipschitz (F R D : ℕ) : ℕ := (64 + 2 * F * R) * D + D ^ 2
def mesh (F R D S : ℕ) : ℕ := 48 * R * lipschitz F R D * volume R * S
def accuracy (R D S : ℕ) : ℕ := 32 * D * volume R * S
def kernelPrecision (R D S : ℕ) : ℕ := 4 * D ^ 2 * volume R * S

theorem dyadic_le_inverse (b : ℕ) : (2 : ℝ)⁻¹ ^ b ≤ ((b : ℝ) + 1)⁻¹ := by
  have hb : (b : ℝ) + 1 ≤ (2 : ℝ) ^ b := by
    exact_mod_cast Nat.succ_le_of_lt b.lt_two_pow_self
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hb

theorem scalar_budget {R D L S V N Q : ℝ} {b : ℕ}
    (hR : 0 < R) (hD : 0 < D) (hL : 0 < L) (hS : 0 < S)
    (hV : V = (2 * R) ^ 6) (hN : N = 48 * R * L * V * S)
    (hQ : Q = 32 * D * V * S) (hb : (b : ℝ) = 4 * D ^ 2 * V * S) :
    V * (6 * L * (2 * R / N) + 8 * D * (Q + 1)⁻¹ + D ^ 2 * (2 : ℝ)⁻¹ ^ b) ≤
      3 * (4 * S)⁻¹ := by
  have hV0 : 0 < V := by rw [hV]; positivity
  have hN0 : 0 < N := by rw [hN]; positivity
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hb0 : (0 : ℝ) < b := by rw [hb]; positivity
  have hmesh : V * (6 * L * (2 * R / N)) = (4 * S)⁻¹ := by
    rw [hN]
    field_simp [hR.ne', hL.ne', hV0.ne', hS.ne']
    ring
  have hsample : V * (8 * D * (Q + 1)⁻¹) ≤ (4 * S)⁻¹ := by
    calc
      _ ≤ V * (8 * D * Q⁻¹) := by
        gcongr
        linarith
      _ = _ := by
        rw [hQ]
        field_simp [hD.ne', hV0.ne', hS.ne']
        ring
  have hkernel : V * (D ^ 2 * (2 : ℝ)⁻¹ ^ b) ≤ (4 * S)⁻¹ := by
    calc
      _ ≤ V * (D ^ 2 * ((b : ℝ) + 1)⁻¹) := by
        gcongr
        exact dyadic_le_inverse b
      _ ≤ V * (D ^ 2 * (b : ℝ)⁻¹) := by
        gcongr
        linarith
      _ = _ := by
        rw [hb]
        field_simp [hD.ne', hV0.ne', hS.ne']
  nlinarith

end ContinuumCoulomb.CoulombQuadratureSchedule

end

end OAI
