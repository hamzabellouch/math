import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedOrbitalNuclearError

namespace OAI

/-! A rational mesh suffices for the stronger compressed error. Taking
h = R^-9 balances fourth-order cubature with the H1 cutoff tail. -/

noncomputable section
namespace ContinuumCoulomb

theorem nuclear_mesh_balance {R a b c q p : ℝ} (hR : 1 ≤ R)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hp : 0 ≤ p) :
    (a*p*R^3+b*R^6+c*R^3)*(1/R^9)^4+q*(1/R^9)^2/R^12 ≤
      (a*p+b+c+q)/R^30 := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have he : (a*p*R^3+b*R^6+c*R^3)*(1/R^9)^4+q*(1/R^9)^2/R^12 =
      a*p/R^33+b/R^30+c/R^33+q/R^30 := by
    field_simp [ne_of_gt hR0]
  rw [he]
  have hpow : R^30 ≤ R^33 := pow_le_pow_right₀ hR (by norm_num)
  have ha' := div_le_div_of_nonneg_left (mul_nonneg ha hp) (pow_pos hR0 30) hpow
  have hc' := div_le_div_of_nonneg_left hc (pow_pos hR0 30) hpow
  calc
    _ ≤ a*p/R^30+b/R^30+c/R^30+q/R^30 := by linarith
    _ = _ := by ring

theorem nuclear_mesh_balance_scaled {R a b c q p rho : ℝ} (hR : 1 ≤ R)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hp : 0 ≤ p) (hrho : 0 ≤ rho) :
    (8/rho)*R^27*((a*p*R^3+b*R^6+c*R^3)*(1/R^9)^4+q*(1/R^9)^2/R^12) ≤
      (8/rho)*(a*p+b+c+q)/R^3 := by
  have he := mul_le_mul_of_nonneg_left (nuclear_mesh_balance hR ha hc hp (b := b) (q := q))
    (show 0 ≤ (8/rho)*R^27 by positivity)
  apply he.trans_eq
  have hR0 : R ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hR)
  field_simp [hR0]

end ContinuumCoulomb

end

end OAI
