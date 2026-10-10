import OAI.Geometry.RCD.Transport.RadialTransportEstimate

namespace OAI

/-! # The outer-ball estimate for an unnormalized radial residual -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

omit [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
/-- Positivity of the actual cutoff converts annular energy to the
larger-ball norm. The inner sphere is harmless under Bishop--Gromov. -/
theorem radial_transport_outer_from_energy {n : ℕ} {R : ℝ} (hR : 2 ≤ R)
    (z : X) {w : X → ℝ} (hw : MemLp w 2 μ) (hsphere : μ (sphere z R) = 0) :
    let β := transportCutoffExponent n
    let m := ((2 * R) ^ (-β) - (3 * R) ^ (-β)) / β
    m * (∫ x in ball z (2 * R), (w x) ^ 2 ∂μ) ≤
      m * (∫ x in ball z R, (w x) ^ 2 ∂μ) +
        ∫ x in ball z (4 * R), transportEnergyWeight n R z x * (w x) ^ 2 ∂μ := by
  dsimp only
  let m := ((2 * R) ^ (-transportCutoffExponent n) - (3 * R) ^ (-transportCutoffExponent n)) /
    transportCutoffExponent n
  let ν := μ.restrict (ball z (4 * R))
  have hnot : ∀ᵐ x ∂ν, dist z x ≠ R := by
    have hh := ae_restrict_of_ae (s := ball z (4 * R)) (measure_eq_zero_iff_ae_notMem.mp hsphere)
    filter_upwards [hh] with x hx
    simpa only [mem_sphere, dist_comm] using hx
  have hR0 : 0 < R := by linarith
  have hbound := hnot.mono fun x hx =>
    (radial_transport_weight_geometry (n := n) hR (a := 0) le_rfl (by positivity) z x hx).1
  have hi : Integrable (fun x => transportEnergyWeight n R z x * (w x) ^ 2) ν :=
    (hw.restrict (ball z (4 * R))).integrable_sq.bdd_mul (transportEnergyWeight_measurable n hR0 z).aestronglyMeasurable
      (hbound.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)
  have hi₁ := ((hw.restrict (ball z (4 * R))).integrable_sq.indicator
    (s := ball z (2 * R)) isOpen_ball.measurableSet).const_mul m
  have hi₂ := ((hw.restrict (ball z (4 * R))).integrable_sq.indicator
    (s := ball z R) isOpen_ball.measurableSet).const_mul m
  have hp : ∀ᵐ x ∂ν, m * (ball z (2 * R)).indicator (fun x => (w x) ^ 2) x ≤
      m * (ball z R).indicator (fun x => (w x) ^ 2) x +
        transportEnergyWeight n R z x * (w x) ^ 2 := by
    filter_upwards [hnot] with x hx
    have hh := mul_le_mul_of_nonneg_right (radial_transport_interior_weight (n := n) hR z x hx)
      (sq_nonneg (w x))
    dsimp only [m]
    by_cases h₁ : x ∈ ball z R <;> by_cases h₂ : x ∈ ball z (2 * R) <;>
      simp [indicator, h₁, h₂] at hh ⊢ <;> nlinarith only [hh]
  have h := integral_mono_ae hi₁ (hi₂.add hi) hp
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add hi₂ hi, integral_const_mul,
    integral_indicator isOpen_ball.measurableSet, integral_indicator isOpen_ball.measurableSet] at h
  have h₁ : ball z R ⊆ ball z (4 * R) := ball_subset_ball (by linarith)
  have h₂ : ball z (2 * R) ⊆ ball z (4 * R) := ball_subset_ball (by linarith)
  simpa only [ν, m, Measure.restrict_restrict_of_subset h₁,
    Measure.restrict_restrict_of_subset h₂] using h

variable (hQ : QuadraticCheegerEnergy μ)

/-- Quantitative radial transport in its squared-norm form. Both error
terms stay quadratic, and all constants are independent of the residual's
possibly tiny inner norm. -/
theorem radial_transport_squared {n : ℕ} {R a : ℝ} (hR : 2 ≤ R)
    (ha : 0 ≤ a) (han : a ≤ (n : ℝ) + 1) (z : X)
    (f w : SobolevSpace μ hQ)
    (hf : IsConstantLaplacianOn μ hQ (ball z (4 * R)) f a)
    (C : ℝ≥0) (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C)
    (F e : X → ℝ) (hF : MemLp F 2 μ) (he : MemLp e 2 μ)
    (heuler : localGamma μ hQ f w =ᵐ[μ.restrict (ball z (4 * R))]
      fun x => SobolevSpace.toLp μ hQ w x + F x / 2)
    (hradial : localGamma μ hQ f (inwardSobolev μ hQ z (3 * R))
      =ᵐ[μ.restrict (ball z (4 * R))] fun x => e x - dist z x)
    (hsphere : μ (sphere z R) = 0) :
    let β := transportCutoffExponent n
    let D := (R ^ (-β) - (3 * R) ^ (-β)) / β
    let Q := R ^ (-(β + 1))
    let m := ((2 * R) ^ (-β) - (3 * R) ^ (-β)) / β
    (∫ x in ball z (2 * R), (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) ≤
      (1 + 2 * ((a + 2) * D + D / 4) / m) *
        (∫ x in ball z R, (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) +
      (2 * D / m) * (∫ x in ball z (4 * R), (F x) ^ 2 ∂μ) +
      (2 * (C : ℝ) ^ 2 * Q / m) * (∫ x in ball z (4 * R), (e x) ^ 2 ∂μ) := by
  dsimp only
  have h₁ := radial_transport_annular_energy μ hQ hR ha han z f w hf C hw F e hF he heuler hradial hsphere
  have h₂ := radial_transport_outer_from_energy μ (n := n) hR z (Lp.memLp (SobolevSpace.toLp μ hQ w)) hsphere
  have hm := (radial_transport_cutoff_lower (n := n) hR z).1
  dsimp only at h₁ h₂ hm
  have hh := h₂.trans (add_le_add le_rfl h₁)
  rw [mul_comm
    (((2 * R) ^ (-transportCutoffExponent n) - (3 * R) ^ (-transportCutoffExponent n)) /
      transportCutoffExponent n)
    (∫ x in ball z (2 * R), (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ)] at hh
  have hdiv := (le_div_iff₀ hm).mpr hh
  refine hdiv.trans_eq ?_
  have halgebra (m A B C x y z : ℝ) (hm : m ≠ 0) :
      (m * x + (A * x + B * y + C * z)) / m =
        (1 + A / m) * x + (B / m) * y + (C / m) * z := by
    field_simp
    ring
  exact halgebra
    (((2 * R) ^ (-transportCutoffExponent n) - (3 * R) ^ (-transportCutoffExponent n)) /
      transportCutoffExponent n)
    (2 * ((a + 2) * ((R ^ (-transportCutoffExponent n) - (3 * R) ^ (-transportCutoffExponent n)) /
      transportCutoffExponent n) +
      ((R ^ (-transportCutoffExponent n) - (3 * R) ^ (-transportCutoffExponent n)) /
        transportCutoffExponent n) / 4))
    (2 * ((R ^ (-transportCutoffExponent n) - (3 * R) ^ (-transportCutoffExponent n)) /
      transportCutoffExponent n))
    (2 * (C : ℝ) ^ 2 * R ^ (-(transportCutoffExponent n + 1)))
    (∫ x in ball z R, (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ)
    (∫ x in ball z (4 * R), (F x) ^ 2 ∂μ)
    (∫ x in ball z (4 * R), (e x) ^ 2 ∂μ) hm.ne'

end RegularPointCoordinates

end

end OAI
