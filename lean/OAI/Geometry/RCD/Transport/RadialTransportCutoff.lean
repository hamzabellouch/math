import OAI.Geometry.RCD.Sobolev.RadialCutoffMass

namespace OAI

/-! # A radial power cutoff with the transport sign

The power cutoff has a compact Sobolev representative and exact
chain rule. Taking exponent 2(n+4) gives the sign needed for radial transport
whenever the fixed inner radius is at least two.
-/

open Metric

noncomputable section
namespace RegularPointCoordinates

def transportCutoffExponent (n : ℕ) : ℝ := 2 * ((n : ℝ) + 4)

theorem transportCutoffExponent_pos (n : ℕ) : 0 < transportCutoffExponent n := by
  dsimp only [transportCutoffExponent]
  positivity

/-- The actual negative radial derivative dominates both its own size
and the zeroth-order transport coefficient throughout the outer annulus. -/
theorem radial_transport_power_sign {n : ℕ} {a R t : ℝ}
    (hR : 2 ≤ R) (ht : R ≤ t) (ha : 0 ≤ a) (han : a ≤ (n : ℝ) + 1) :
    let β := transportCutoffExponent n
    let φ := (t ^ (-β) - (3 * R) ^ (-β)) / β
    t * t ^ (-(β + 1)) - (a + 2) * φ ≥ t ^ (-(β + 1)) + φ := by
  let β := transportCutoffExponent n
  have hβ : 0 < β := transportCutoffExponent_pos n
  have ht0 : 0 < t := by linarith
  have hR0 : 0 ≤ 3 * R := by linarith
  have hpow : t * t ^ (-(β + 1)) = t ^ (-β) := by
    calc
      _ = t ^ (1 : ℝ) * t ^ (-(β + 1)) := by rw [Real.rpow_one]
      _ = t ^ (1 - (β + 1)) := by rw [← Real.rpow_add ht0]; congr 1
      _ = _ := by congr 1; ring
  have hq : 0 ≤ t ^ (-(β + 1)) := Real.rpow_nonneg ht0.le _
  have hV : 0 ≤ t ^ (-β) := Real.rpow_nonneg ht0.le _
  have hW : 0 ≤ (3 * R) ^ (-β) := Real.rpow_nonneg hR0 _
  have hcoeff : (a + 3) / β ≤ 1 / 2 := by
    apply (div_le_iff₀ hβ).mpr
    dsimp only [β, transportCutoffExponent]
    linarith
  have hforcing : (a + 3) * ((t ^ (-β) - (3 * R) ^ (-β)) / β) ≤
      (1 / 2 : ℝ) * t ^ (-β) := by
    calc
      _ ≤ (a + 3) * (t ^ (-β) / β) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact div_le_div_of_nonneg_right (sub_le_self _ hW) hβ.le
      _ = ((a + 3) / β) * t ^ (-β) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hV
  have hhalf : (1 / 2 : ℝ) * t ^ (-β) ≤ (t - 1) * t ^ (-(β + 1)) := by
    have hh := mul_nonneg (show 0 ≤ t - 2 by linarith) hq
    nlinarith only [hpow, hh]
  dsimp only
  change t * t ^ (-(β + 1)) - (a + 2) * ((t ^ (-β) - (3 * R) ^ (-β)) / β) ≥ _
  nlinarith only [hforcing.trans hhalf]

variable {X : Type*} [MetricSpace X]

/-- The radial power cutoff satisfies the coercive transport sign. -/
theorem radial_transport_cutoff_sign {n : ℕ} {a R : ℝ}
    (hR : 2 ≤ R) (ha : 0 ≤ a) (han : a ≤ (n : ℝ) + 1) (z x : X)
    (hinner : R ≤ dist z x) (houter : dist z x ≤ 3 * R) :
    let β := transportCutoffExponent n
    dist z x * (dist z x) ^ (-(β + 1)) -
      (a + 2) * radialPowerRep β R (3 * R) z x ≥
        (dist z x) ^ (-(β + 1)) + radialPowerRep β R (3 * R) z x := by
  dsimp only
  rw [radialPowerRep_annulus (transportCutoffExponent_pos n) (by linarith : 0 < R)
    z x hinner houter]
  exact radial_transport_power_sign hR hinner ha han

end RegularPointCoordinates

end

end OAI
