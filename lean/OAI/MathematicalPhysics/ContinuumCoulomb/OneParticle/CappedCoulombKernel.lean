import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulomb

namespace OAI

/-! A bounded Lipschitz kernel for literal Coulomb quadrature. The original
singular potential differs only inside the cap radius; the next theorem
controls that error by the actual Coulomb mass of the small ball. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def cappedCoulombKernel (ε : ℝ) (x : Position) : ℝ := (max ε ‖x‖)⁻¹

theorem cappedCoulombKernel_nonnegative {ε : ℝ} (hε : 0 < ε) (x : Position) :
    0 ≤ cappedCoulombKernel ε x := by
  unfold cappedCoulombKernel
  exact inv_nonneg.mpr (hε.le.trans (le_max_left _ _))

theorem cappedCoulombKernel_le {ε : ℝ} (hε : 0 < ε) (x : Position) :
    cappedCoulombKernel ε x ≤ ε⁻¹ :=
  inv_anti₀ hε (le_max_left _ _)

theorem cappedCoulombKernel_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (cappedCoulombKernel ε) := by
  apply (continuous_const.max continuous_norm).inv₀
  intro x
  exact (hε.trans_le (le_max_left _ _)).ne'

theorem cappedCoulombKernel_norm_sub {ε : ℝ} (hε : 0 < ε) (x y : Position) :
    |cappedCoulombKernel ε x - cappedCoulombKernel ε y| ≤ ε⁻¹ ^ 2 * ‖x - y‖ := by
  let a := max ε ‖x‖
  let b := max ε ‖y‖
  have ha : 0 < a := hε.trans_le (le_max_left _ _)
  have hb : 0 < b := hε.trans_le (le_max_left _ _)
  have hia : a⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (le_max_left _ _)
  have hib : b⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (le_max_left _ _)
  have hdiff : |a - b| ≤ ‖x - y‖ := by
    have hm := abs_max_sub_max_le_abs ‖x‖ ‖y‖ ε
    rw [max_comm ‖x‖ ε, max_comm ‖y‖ ε] at hm
    exact hm.trans (abs_norm_sub_norm_le x y)
  have he : cappedCoulombKernel ε x - cappedCoulombKernel ε y =
      (b - a) * a⁻¹ * b⁻¹ := by
    change a⁻¹ - b⁻¹ = _
    field_simp [ha.ne', hb.ne']
  rw [he, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr ha),
    abs_of_pos (inv_pos.mpr hb), abs_sub_comm b a]
  calc
    _ ≤ ‖x - y‖ * ε⁻¹ * ε⁻¹ := by gcongr
    _ = _ := by ring

theorem cappedCoulombKernel_difference {ε : ℝ} (hε : 0 < ε)
    (x : Position) (hx : x ≠ 0) :
    |NeutralAtom.coulombKernel x - cappedCoulombKernel ε x| ≤
      (Metric.ball (0 : Position) ε).indicator NeutralAtom.coulombKernel x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  by_cases he : ‖x‖ < ε
  · rw [Set.indicator_of_mem (by simpa only [Metric.mem_ball, dist_zero_right] using he)]
    have hc : cappedCoulombKernel ε x = ε⁻¹ := by
      unfold cappedCoulombKernel
      rw [max_eq_left he.le]
    rw [NeutralAtom.coulombKernel, hc, abs_of_nonneg (sub_nonneg.mpr (inv_anti₀ hn he.le))]
    have hi := inv_nonneg.mpr hε.le
    linarith
  · rw [Set.indicator_of_notMem (by simpa only [Metric.mem_ball, dist_zero_right] using he)]
    simp only [NeutralAtom.coulombKernel, cappedCoulombKernel, max_eq_right (le_of_not_gt he),
      sub_self, abs_zero, le_refl]

def cappedCoulombPotential (ε : ℝ) (ρ : Position → ℝ) (x : Position) : ℝ :=
  ∫ y, cappedCoulombKernel ε (x - y) * ρ y

theorem cappedCoulombPotential_integrable {ε : ℝ} (hε : 0 < ε)
    {ρ : Position → ℝ} (hρ : Integrable ρ) (x : Position) :
    Integrable (fun y => cappedCoulombKernel ε (x - y) * ρ y) := by
  apply hρ.bdd_mul (c := ε⁻¹)
    ((cappedCoulombKernel_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by
    change ‖cappedCoulombKernel ε (x - y)‖ ≤ ε⁻¹
    rw [Real.norm_of_nonneg (cappedCoulombKernel_nonnegative hε _)]
    exact cappedCoulombKernel_le hε _)

theorem cappedCoulombPotential_nonnegative {ε : ℝ} (hε : 0 < ε)
    {ρ : Position → ℝ} (hpos : ∀ x, 0 ≤ ρ x) (x : Position) :
    0 ≤ cappedCoulombPotential ε ρ x :=
  integral_nonneg (fun y => mul_nonneg (cappedCoulombKernel_nonnegative hε _) (hpos y))

theorem cappedCoulombPotential_le {ε : ℝ} (hε : 0 < ε)
    {ρ : Position → ℝ} (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x) (x : Position) :
    cappedCoulombPotential ε ρ x ≤ ε⁻¹ * ∫ y, ρ y := by
  have h := integral_mono (cappedCoulombPotential_integrable hε hρ x)
    (hρ.const_mul ε⁻¹) (fun y =>
      mul_le_mul_of_nonneg_right (cappedCoulombKernel_le hε _) (hpos y))
  simpa only [cappedCoulombPotential, integral_const_mul] using h

theorem cappedCoulombPotential_norm_sub {ε : ℝ} (hε : 0 < ε)
    {ρ : Position → ℝ} (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x) (x x' : Position) :
    ‖cappedCoulombPotential ε ρ x - cappedCoulombPotential ε ρ x'‖ ≤
      (ε⁻¹ ^ 2 * ∫ y, ρ y) * ‖x - x'‖ := by
  unfold cappedCoulombPotential
  rw [← integral_sub (cappedCoulombPotential_integrable hε hρ x)
    (cappedCoulombPotential_integrable hε hρ x')]
  have h := norm_integral_le_of_norm_le
    (f := fun y => cappedCoulombKernel ε (x - y) * ρ y -
      cappedCoulombKernel ε (x' - y) * ρ y)
    (hρ.const_mul (ε⁻¹ ^ 2 * ‖x - x'‖))
    (Filter.Eventually.of_forall (fun y => by
      rw [← sub_mul, norm_mul, Real.norm_of_nonneg (hpos y), Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_right _ (hpos y)
      simpa only [sub_sub_sub_cancel_right] using
        cappedCoulombKernel_norm_sub hε (x - y) (x' - y)))
  rw [integral_const_mul] at h
  convert h using 1
  ring

theorem cappedCoulombPotential_continuous {ε : ℝ} (hε : 0 < ε)
    {ρ : Position → ℝ} (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x) :
    Continuous (cappedCoulombPotential ε ρ) := by
  have hc : 0 ≤ ε⁻¹ ^ 2 * ∫ y, ρ y :=
    mul_nonneg (sq_nonneg _) (integral_nonneg hpos)
  exact (show LipschitzWith ⟨ε⁻¹ ^ 2 * ∫ y, ρ y, hc⟩ (cappedCoulombPotential ε ρ) from
    lipschitzWith_iff_norm_sub_le.mpr (cappedCoulombPotential_norm_sub hε hρ hpos)).continuous

theorem cappedCoulombPotential_error {ε B : ℝ} (hε : 0 < ε)
    {ρ : Position → ℝ} (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hbound : ∀ x, ρ x ≤ B) (x : Position) :
    |NeutralAtom.potentialOf ρ x - cappedCoulombPotential ε ρ x| ≤
      B * NeutralAtom.kernelBallMass ε := by
  have hi := (NeutralAtom.bounded_density_convolution NeutralAtom.measurable_coulombKernel
    NeutralAtom.coulombKernel_nonneg (NeutralAtom.coulombKernel_integrableOn_ball 1)
    (fun _ => NeutralAtom.coulombKernel_le_one) hρ hpos hbound x).1
  rw [NeutralAtom.potentialOf, cappedCoulombPotential,
    ← integral_sub hi (cappedCoulombPotential_integrable hε hρ x)]
  have hd := norm_integral_le_of_norm_le
    (f := fun y => NeutralAtom.coulombKernel (x - y) * ρ y -
      cappedCoulombKernel ε (x - y) * ρ y)
    ((NeutralAtom.translated_kernel_indicator_integrable x ε).const_mul B)
    (by
      filter_upwards [volume.ae_ne x] with y hy
      rw [← sub_mul, norm_mul, Real.norm_of_nonneg (hpos y), Real.norm_eq_abs]
      have hc := cappedCoulombKernel_difference hε (x - y) (sub_ne_zero.mpr hy.symm)
      have hs : (Metric.ball (0 : Position) ε).indicator NeutralAtom.coulombKernel (x - y) =
          (Metric.ball x ε).indicator (fun z => NeutralAtom.coulombKernel (x - z)) y := by
        rw [NeutralAtom.translated_kernel_indicator_eq]
      rw [hs] at hc
      have hp : 0 ≤ (Metric.ball x ε).indicator
          (fun z => NeutralAtom.coulombKernel (x - z)) y :=
        Set.indicator_nonneg (fun z _ => NeutralAtom.coulombKernel_nonneg (x - z)) y
      calc
        _ ≤ (Metric.ball x ε).indicator
            (fun z => NeutralAtom.coulombKernel (x - z)) y * B :=
          mul_le_mul hc (hbound y) (hpos y) hp
        _ = _ := mul_comm _ _)
  simpa only [Real.norm_eq_abs, integral_const_mul,
    NeutralAtom.translated_kernel_indicator_integral] using hd

end ContinuumCoulomb

end

end OAI
