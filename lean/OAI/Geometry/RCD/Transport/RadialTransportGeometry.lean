import OAI.Geometry.RCD.Transport.RadialTransportWeight

namespace OAI

/-! # Geometric weights for the radial transport energy -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

def transportEnergyWeight (n : ℕ) (R : ℝ) (z : X) (x : X) : ℝ :=
  (transportAnnulus z R).indicator (fun x =>
    transportDerivativeWeight n R z x + radialPowerRep (transportCutoffExponent n) R (3 * R) z x) x

/-- The sign and the two comparisons needed by the energy argument hold
for the constructed weights. Only the inner sphere is excluded. -/
theorem radial_transport_weight_geometry {n : ℕ} {R a : ℝ} (hR : 2 ≤ R)
    (ha : 0 ≤ a) (han : a ≤ (n : ℝ) + 1) (z x : X) (hne : dist z x ≠ R) :
    let β := transportCutoffExponent n
    let D := (R ^ (-β) - (3 * R) ^ (-β)) / β
    let Q := R ^ (-(β + 1))
    let φ := radialPowerRep β R (3 * R) z x
    let ρ := transportDerivativeWeight n R z x
    let ζ := transportEnergyWeight n R z x
    let I := (ball z R).indicator (fun _ => (1 : ℝ)) x
    (0 ≤ ζ ∧ ζ ≤ D + Q) ∧ ρ ≤ ζ ∧ φ ≤ ζ + D * I ∧
      ζ ≤ (a + 2) * D * I - (a + 2) * φ + ρ * dist z x := by
  dsimp only
  have hR0 : 0 < R := by linarith
  have hβ := transportCutoffExponent_pos n
  have hφ := radialPowerRep_bounds hβ hR0 (by linarith : R ≤ 3 * R) z x
  have hρ := transportDerivativeWeight_bounds n hR0 z x
  have hD : 0 ≤ (R ^ (-transportCutoffExponent n) - (3 * R) ^ (-transportCutoffExponent n)) /
      transportCutoffExponent n := by
    have hh := (radialPowerRep_bounds hβ hR0 (by linarith : R ≤ 3 * R) z z).1
    rwa [radialPowerRep_inner hβ hR0 (by linarith : R ≤ 3 * R) z z (by simp; linarith)] at hh
  by_cases hinner : dist z x < R
  · have hmem : x ∈ ball z R := by simpa only [mem_ball, dist_comm] using hinner
    have hnann : x ∉ transportAnnulus z R := fun hx => (not_lt_of_ge hx.1.le) hinner
    simp only [transportEnergyWeight, transportDerivativeWeight, indicator_of_notMem hnann,
      indicator_of_mem hmem, zero_add, zero_mul]
    rw [radialPowerRep_inner hβ hR0 (by linarith : R ≤ 3 * R) z x hinner.le]
    constructor
    · exact ⟨le_rfl, add_nonneg hD (Real.rpow_nonneg hR0.le _)⟩
    · constructor
      · exact le_rfl
      · constructor <;> nlinarith
  · have hrx : R < dist z x := lt_of_le_of_ne (le_of_not_gt hinner) hne.symm
    have hnmem : x ∉ ball z R := by simpa only [mem_ball, dist_comm, not_lt] using hrx.le
    by_cases hout : dist z x < 3 * R
    · have hann : x ∈ transportAnnulus z R := ⟨hrx, hout⟩
      simp only [transportEnergyWeight, indicator_of_mem hann, indicator_of_notMem hnmem,
        mul_zero, add_zero]
      constructor
      · exact ⟨add_nonneg hρ.1 hφ.1, by linarith [hρ.2, hφ.2]⟩
      · constructor
        · linarith only [hφ.1]
        · constructor
          · linarith only [hρ.1]
          · have hs := radial_transport_cutoff_sign hR ha han z x hrx.le hout.le
            change (dist z x) * (dist z x) ^ (-(transportCutoffExponent n + 1)) -
              (a + 2) * radialPowerRep (transportCutoffExponent n) R (3 * R) z x ≥
                (dist z x) ^ (-(transportCutoffExponent n + 1)) +
                  radialPowerRep (transportCutoffExponent n) R (3 * R) z x at hs
            rw [transportDerivativeWeight, indicator_of_mem hann]
            linarith only [hs]
    · have hnann : x ∉ transportAnnulus z R := fun hx => hout hx.2
      rw [transportEnergyWeight, indicator_of_notMem hnann,
        transportDerivativeWeight, indicator_of_notMem hnann,
        radialPowerRep_zero (by linarith : R ≤ 3 * R) z x (le_of_not_gt hout),
        indicator_of_notMem hnmem]
      constructor
      · exact ⟨le_rfl, add_nonneg hD (Real.rpow_nonneg hR0.le _)⟩
      · constructor
        · exact le_rfl
        · constructor <;> simp

/-- The positive cutoff controls the desired larger ball by the inner
ball and the same annular energy. -/
theorem radial_transport_interior_weight {n : ℕ} {R : ℝ} (hR : 2 ≤ R)
    (z x : X) (hne : dist z x ≠ R) :
    let β := transportCutoffExponent n
    let m := ((2 * R) ^ (-β) - (3 * R) ^ (-β)) / β
    m * (ball z (2 * R)).indicator (fun _ => (1 : ℝ)) x ≤
      m * (ball z R).indicator (fun _ => (1 : ℝ)) x + transportEnergyWeight n R z x := by
  dsimp only
  have hlow := radial_transport_cutoff_lower (n := n) hR z
  have hβ := transportCutoffExponent_pos n
  have hR0 : 0 < R := by linarith
  by_cases hinner : dist z x < R
  · have hi : x ∈ ball z R := by simpa only [mem_ball, dist_comm] using hinner
    have ho : x ∈ ball z (2 * R) := ball_subset_ball (by linarith) hi
    have hnann : x ∉ transportAnnulus z R := fun hx => (not_lt_of_ge hx.1.le) hinner
    simp only [indicator_of_mem hi, indicator_of_mem ho, transportEnergyWeight,
      indicator_of_notMem hnann, add_zero, le_refl]
  · have hi : x ∉ ball z R := by simpa only [mem_ball, dist_comm] using hinner
    have hrx : R < dist z x := lt_of_le_of_ne (le_of_not_gt hinner) hne.symm
    by_cases ho : x ∈ ball z (2 * R)
    · have hdx : dist z x < 2 * R := by simpa only [mem_ball, dist_comm] using ho
      have hann : x ∈ transportAnnulus z R := ⟨hrx, by linarith⟩
      simp only [indicator_of_mem ho, indicator_of_notMem hi, mul_one, mul_zero,
        zero_add, transportEnergyWeight, indicator_of_mem hann]
      exact (hlow.2 x hdx.le).trans (le_add_of_nonneg_left
        (transportDerivativeWeight_bounds n hR0 z x).1)
    · simp only [indicator_of_notMem hi, indicator_of_notMem ho, mul_zero, zero_add]
      by_cases hann : x ∈ transportAnnulus z R
      · simp only [transportEnergyWeight, indicator_of_mem hann]
        exact add_nonneg (transportDerivativeWeight_bounds n hR0 z x).1
          (radialPowerRep_bounds hβ hR0 (by linarith : R ≤ 3 * R) z x).1
      · simp only [transportEnergyWeight, indicator_of_notMem hann, le_refl]

variable [MeasurableSpace X] [BorelSpace X]

theorem transportEnergyWeight_measurable (n : ℕ) {R : ℝ} (hR : 0 < R) (z : X) :
    Measurable (transportEnergyWeight n R z) :=
  ((transportDerivativeWeight_measurable n R z).add
    (radialPowerRep_lipschitz (transportCutoffExponent_pos n) hR z).continuous.measurable).indicator
      (transportAnnulus_measurableSet z R)

end RegularPointCoordinates

end

end OAI
