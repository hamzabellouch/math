import OAI.Geometry.RCD.Transport.RadialTransportGeometry

namespace OAI

/-! # Radial transport weights at arbitrary positive radius -/

open Set Metric

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

/-- Multiplying the annular derivative by the physical radius preserves
coercivity when the working balls shrink. -/
def scaledTransportWeight (n : ℕ) (R : ℝ) (z x : X) : ℝ :=
  (R / 2) * transportDerivativeWeight n R z x

theorem scaled_transport_weight_geometry {n : ℕ} {R a : ℝ} (hR : 0 < R)
    (ha : 0 ≤ a) (han : a ≤ (n : ℝ) + 1) (z x : X) (hne : dist z x ≠ R) :
    let β := transportCutoffExponent n
    let D := (R ^ (-β) - (3 * R) ^ (-β)) / β
    let Q := R ^ (-(β + 1))
    let φ := radialPowerRep β R (3 * R) z x
    let ρ := transportDerivativeWeight n R z x
    let ζ := scaledTransportWeight n R z x
    let I := (ball z R).indicator (fun _ => (1 : ℝ)) x
    (0 ≤ ζ ∧ ζ ≤ (R / 2) * Q) ∧ φ ≤ ζ + D * I ∧
      ζ ≤ (a + 2) * D * I - (a + 2) * φ + ρ * dist z x := by
  dsimp only
  let β := transportCutoffExponent n
  have hβ : 0 < β := transportCutoffExponent_pos n
  have hβsix : 6 ≤ β := by
    dsimp only [β, transportCutoffExponent]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hφ := radialPowerRep_bounds hβ hR (by linarith : R ≤ 3 * R) z x
  have hρ := transportDerivativeWeight_bounds n hR z x
  have hζ : 0 ≤ scaledTransportWeight n R z x ∧
      scaledTransportWeight n R z x ≤ (R / 2) * R ^ (-(β + 1)) :=
    ⟨mul_nonneg (by positivity) hρ.1,
      mul_le_mul_of_nonneg_left hρ.2 (by positivity)⟩
  refine ⟨hζ, ?_⟩
  by_cases hin : dist z x < R
  · have hm : x ∈ ball z R := by simpa only [mem_ball, dist_comm] using hin
    have hn : x ∉ transportAnnulus z R := fun hx => (not_lt_of_ge hx.1.le) hin
    simp only [scaledTransportWeight, transportDerivativeWeight, indicator_of_notMem hn,
      mul_zero, indicator_of_mem hm, mul_one, zero_add]
    rw [radialPowerRep_inner hβ hR (by linarith : R ≤ 3 * R) z x hin.le]
    exact ⟨le_rfl, by dsimp only [β]; ring_nf; exact le_rfl⟩
  · have hRx : R < dist z x := lt_of_le_of_ne (le_of_not_gt hin) hne.symm
    have hm : x ∉ ball z R := by simpa only [mem_ball, dist_comm, not_lt] using hRx.le
    by_cases hout : dist z x < 3 * R
    · have hann : x ∈ transportAnnulus z R := ⟨hRx, hout⟩
      have ht : 0 < dist z x := hR.trans hRx
      have hpow : dist z x * (dist z x) ^ (-(β + 1)) = (dist z x) ^ (-β) := by
        calc
          _ = (dist z x) ^ (1 : ℝ) * (dist z x) ^ (-(β + 1)) := by rw [Real.rpow_one]
          _ = (dist z x) ^ (1 - (β + 1)) := by rw [← Real.rpow_add ht]; congr 1
          _ = _ := by congr 1; ring
      have hq : 0 ≤ (dist z x) ^ (-(β + 1)) := Real.rpow_nonneg ht.le _
      have hV : 0 ≤ dist z x * (dist z x) ^ (-(β + 1)) := mul_nonneg ht.le hq
      have hp : radialPowerRep β R (3 * R) z x ≤
          dist z x * (dist z x) ^ (-(β + 1)) / β := by
        rw [radialPowerRep_annulus hβ hR z x hRx.le hout.le, hpow]
        exact div_le_div_of_nonneg_right
          (sub_le_self _ (Real.rpow_nonneg (by positivity) _)) hβ.le
      have hcoef : (a + 2) / β ≤ (1 / 2 : ℝ) := by
        apply (div_le_iff₀ hβ).mpr
        dsimp only [β, transportCutoffExponent]
        linarith
      have hsmall : 3 / β ≤ (1 / 2 : ℝ) := by
        apply (div_le_iff₀ hβ).mpr
        linarith
      have hpbound : radialPowerRep β R (3 * R) z x ≤
          (R / 2) * (dist z x) ^ (-(β + 1)) := by
        calc
          _ ≤ _ := hp
          _ ≤ (3 * R * (dist z x) ^ (-(β + 1))) / β :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hout.le hq) hβ.le
          _ = (3 / β) * (R * (dist z x) ^ (-(β + 1))) := by ring
          _ ≤ (1 / 2 : ℝ) * (R * (dist z x) ^ (-(β + 1))) :=
            mul_le_mul_of_nonneg_right hsmall (mul_nonneg hR.le hq)
          _ = _ := by ring
      have hap : (a + 2) * radialPowerRep β R (3 * R) z x ≤
          (1 / 2 : ℝ) * (dist z x * (dist z x) ^ (-(β + 1))) := by
        calc
          _ ≤ (a + 2) * (dist z x * (dist z x) ^ (-(β + 1)) / β) :=
            mul_le_mul_of_nonneg_left hp (by linarith)
          _ = ((a + 2) / β) * (dist z x * (dist z x) ^ (-(β + 1))) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hV
      simp only [scaledTransportWeight, transportDerivativeWeight, indicator_of_mem hann,
        indicator_of_notMem hm, mul_zero, add_zero]
      refine ⟨hpbound, ?_⟩
      have hh := mul_le_mul_of_nonneg_right hRx.le hq
      nlinarith only [hap, hh]
    · have hn : x ∉ transportAnnulus z R := fun hx => hout hx.2
      rw [scaledTransportWeight, transportDerivativeWeight, indicator_of_notMem hn,
        radialPowerRep_zero (by linarith : R ≤ 3 * R) z x (le_of_not_gt hout),
        indicator_of_notMem hm]
      simp

theorem scaled_transport_interior_weight {n : ℕ} {R : ℝ} (hR : 0 < R)
    (z x : X) (hne : dist z x ≠ R) :
    let β := transportCutoffExponent n
    let m := (R / 2) * (2 * R) ^ (-(β + 1))
    m * (ball z (2 * R)).indicator (fun _ => (1 : ℝ)) x ≤
      m * (ball z R).indicator (fun _ => (1 : ℝ)) x + scaledTransportWeight n R z x := by
  dsimp only
  have hρ := (transportDerivativeWeight_bounds n hR z x).1
  by_cases hin : x ∈ ball z R
  · have ho : x ∈ ball z (2 * R) := ball_subset_ball (by linarith) hin
    simp only [indicator_of_mem hin, indicator_of_mem ho, mul_one]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hρ)
  · have hRx : R < dist z x := lt_of_le_of_ne
      (by simpa only [mem_ball, dist_comm, not_lt] using hin) hne.symm
    by_cases ho : x ∈ ball z (2 * R)
    · have hx : dist z x < 2 * R := by simpa only [mem_ball, dist_comm] using ho
      have hann : x ∈ transportAnnulus z R := ⟨hRx, by linarith⟩
      simp only [indicator_of_notMem hin, indicator_of_mem ho, mul_zero, mul_one,
        zero_add, scaledTransportWeight, transportDerivativeWeight, indicator_of_mem hann]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (hR.trans hRx) hx.le
          (by linarith [transportCutoffExponent_pos n])) (by positivity)
    · simp only [indicator_of_notMem hin, indicator_of_notMem ho, mul_zero, zero_add]
      exact mul_nonneg (by positivity) hρ

end RegularPointCoordinates

end

end OAI
