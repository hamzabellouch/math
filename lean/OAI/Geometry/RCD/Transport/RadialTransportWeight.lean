import OAI.Geometry.RCD.Transport.RadialTransportCutoffBounds

namespace OAI

/-! # The actual annular derivative weight of the transport cutoff -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

def transportAnnulus (z : X) (R : ℝ) : Set X :=
  {x | R < dist z x ∧ dist z x < 3 * R}

def transportDerivativeWeight (n : ℕ) (R : ℝ) (z : X) (x : X) : ℝ :=
  (transportAnnulus z R).indicator (fun x => (dist z x) ^ (-(transportCutoffExponent n + 1))) x

theorem transportDerivativeWeight_bounds (n : ℕ) {R : ℝ} (hR : 0 < R) (z x : X) :
    0 ≤ transportDerivativeWeight n R z x ∧
      transportDerivativeWeight n R z x ≤ R ^ (-(transportCutoffExponent n + 1)) := by
  by_cases hx : x ∈ transportAnnulus z R
  · simp only [transportDerivativeWeight, indicator_of_mem hx]
    exact ⟨Real.rpow_nonneg dist_nonneg _,
      Real.rpow_le_rpow_of_nonpos hR hx.1.le (by linarith [transportCutoffExponent_pos n])⟩
  · simp only [transportDerivativeWeight, indicator_of_notMem hx]
    exact ⟨le_rfl, Real.rpow_nonneg hR.le _⟩

variable [MeasurableSpace X] [BorelSpace X]

theorem transportAnnulus_measurableSet (z : X) (R : ℝ) : MeasurableSet (transportAnnulus z R) :=
  (isOpen_lt continuous_const (continuous_const.dist continuous_id)).measurableSet.inter
    (isOpen_lt (continuous_const.dist continuous_id) continuous_const).measurableSet

theorem transportDerivativeWeight_measurable (n : ℕ) (R : ℝ) (z : X) :
    Measurable (transportDerivativeWeight n R z) :=
  ((continuous_const.dist continuous_id).measurable.pow_const _).indicator
    (transportAnnulus_measurableSet z R)

variable [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

/-- The exact derivative formula, including the constant inner part and
the zero exterior part. The error is the actual radial pairing defect. -/
theorem radial_transport_cutoff_gamma (n : ℕ) {R : ℝ} (hR : 0 < R) (z : X)
    (f : SobolevSpace μ hQ) :
    let η := radialPowerTest μ hQ (inwardSobolev μ hQ z (3 * R))
      (transportCutoffExponent_pos n) hR (by linarith : R ≤ 3 * R)
    localGamma μ hQ f η =ᵐ[μ] fun x =>
      transportDerivativeWeight n R z x *
        (localGamma μ hQ f (inwardSobolev μ hQ z (3 * R)) x) := by
  dsimp only
  filter_upwards [radialPowerTest_gamma μ hQ f (inwardSobolev μ hQ z (3 * R))
      ((inwardSobolev_bounds μ hQ z (by linarith : 0 ≤ 3 * R)).mono fun _ hx => hx.1)
      (transportCutoffExponent_pos n) hR (by linarith : R ≤ 3 * R),
    inwardSobolev_coe μ hQ z (3 * R),
    localGamma_comm μ hQ f (inwardSobolev μ hQ z (3 * R)),
    localGamma_zero_on_level μ hQ (inwardSobolev μ hQ z (3 * R)) f 0]
      with x hγ hu hcomm hz
  rw [hγ, hu]
  by_cases hout : dist z x < 3 * R
  · have hu' : inwardDistance z (3 * R) x = 3 * R - dist z x :=
      max_eq_left (by linarith)
    rw [hu']
    by_cases hin : R < dist z x
    · have hx : x ∈ transportAnnulus z R := ⟨hin, hout⟩
      rw [ite_eq_left (by linarith), transportDerivativeWeight, indicator_of_mem hx]
      congr 1
      simp only [radialPowerWeight, sub_sub_cancel, max_eq_right hin.le]
    · have hx : x ∉ transportAnnulus z R := fun h => hin h.1
      rw [ite_eq_right (by linarith), transportDerivativeWeight, indicator_of_notMem hx, zero_mul]
  · have hx : x ∉ transportAnnulus z R := fun h => hout h.2
    have hu' : inwardDistance z (3 * R) x = 0 := max_eq_right (by linarith)
    have hzero := hcomm.trans (hz (hu.trans hu'))
    rw [hu', ite_eq_left (by linarith), hzero, mul_zero,
      transportDerivativeWeight, indicator_of_notMem hx, zero_mul]

end RegularPointCoordinates

end

end OAI
