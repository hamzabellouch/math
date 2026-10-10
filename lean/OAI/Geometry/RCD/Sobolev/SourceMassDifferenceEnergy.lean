import OAI.Geometry.RCD.Harmonic.CaccioppoliSourceMass

namespace OAI

/-! # Local gradient differences controlled by value error and source mass -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem source_mass_difference_energy (u w η : SobolevSpace μ Q) (d e : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ Q u d) (he : IsWeakLaplacian μ Q w e)
    {v : X → ℝ} {L B M : ℝ≥0}
    (hv : LipschitzWith L v) (hs : HasCompactSupport v)
    (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (hη : SobolevSpace.toLp μ Q η =ᵐ[μ] v)
    (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ Q η x| ≤ M)
    {D A : ℝ} (hD : 0 ≤ D) (_hA : 0 ≤ A)
    (hvalue : ∀ᵐ x ∂μ, v x ≠ 0 →
      |SobolevSpace.toLp μ Q u x-SobolevSpace.toLp μ Q w x| ≤ D)
    (hdi : Integrable (fun x => (v x)^2*|d x|) μ)
    (hei : Integrable (fun x => (v x)^2*|e x|) μ)
    (hdA : (∫ x, (v x)^2*|d x| ∂μ) ≤ A)
    (heA : (∫ x, (v x)^2*|e x| ∂μ) ≤ A) :
    weightedGamma μ Q (fun x => (v x)^2) (u-w) (u-w) ≤
      4*D*A+4*D^2*(∫ x, (SobolevSpace.minimalSlope μ Q η x)^2 ∂μ) := by
  have hde : IsWeakLaplacian μ Q (u-w) (d-e) := by
    simpa only [neg_one_smul,sub_eq_add_neg] using hd.add μ Q (he.smul μ Q (-1))
  have habs (x : X) : |d x-e x| ≤ |d x|+|e x| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (d x) (-(e x))
  have hdom : ∀ᵐ x ∂μ, ‖(v x)^2*|(d-e) x|‖ ≤ (v x)^2*|d x|+(v x)^2*|e x| := by
    filter_upwards [Lp.coeFn_sub d e] with x hx
    rw [hx,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left (habs x) (sq_nonneg (v x))).trans_eq (mul_add _ _ _)
  have hi : Integrable (fun x => (v x)^2*|(d-e) x|) μ :=
    (hdi.add hei).mono'
      ((hv.continuous.aestronglyMeasurable.pow 2).mul (continuous_abs.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (d-e)))) hdom
  have hmass : (∫ x, (v x)^2*|(d-e) x| ∂μ) ≤ 2*A := by
    have hm := integral_mono_ae hi (hdi.add hei) (hdom.mono fun x hx =>
      (le_abs_self ((v x)^2*|(d-e) x|)).trans hx)
    simp only [Pi.add_apply] at hm
    rw [integral_add hdi hei] at hm
    linarith
  have hval : ∀ᵐ x ∂μ, v x ≠ 0 → |SobolevSpace.toLp μ Q (u-w) x| ≤ D := by
    simp only [map_sub]
    filter_upwards [hvalue,Lp.coeFn_sub (SobolevSpace.toLp μ Q u) (SobolevSpace.toLp μ Q w)]
      with x hx heq
    rw [heq]
    exact hx
  have hc := caccioppoli_source_mass μ Q (u-w) η (d-e) hde hv hs hb hn hη hgrad hD hval hi
  have hid : weightedGamma μ Q (fun x => (v x)^2) (u-w) (u-w) =
      ∫ x, (SobolevSpace.toLp μ Q η x)^2*(SobolevSpace.minimalSlope μ Q (u-w) x)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hη,localGamma_self μ Q (u-w)] with x hx hg
    rw [hx,hg]
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_left hmass (by linarith : 0 ≤ 2*D)]

end RegularPointCoordinates

end

end OAI
