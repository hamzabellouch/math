import OAI.Geometry.RCD.Sobolev.PositiveSourceGradient

namespace OAI

/-! # The balanced positive-source gradient estimate -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

def balancedGradientConstant (d q : ℝ) : ℝ :=
  2 ^ q * (1 + q * (q⁻¹ + (d - q)⁻¹)) / (q - 1)

theorem balancedGradientConstant_pos {d q : ℝ} (hq : 1 < q) (hqd : q < d) :
    0 < balancedGradientConstant d q := by
  unfold balancedGradientConstant
  positivity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- When the tail coefficient is at most the domain volume, the weighted
energy argument gives the correctly homogeneous square-gradient estimate. -/
theorem balanced_positive_source_gradient (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (H : SobolevSpace.dirichlet μ hQ Ω)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x)
    {d q C P : ℝ} (hq : 1 < q) (hqd : q < d) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        C * energyForm μ hQ φ.val φ.val)
    (hsource : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, ∀ t : ℝ, 0 ≤ t →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧ SobolevSpace.toLp μ hQ φ.val x ≤ t) →
      energyForm μ hQ H.val φ.val ≤ P * t)
    (hbalance : (C * P) ^ d ≤ μ.real Ω) :
    IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ H.val x) Ω μ ∧
      (∫ x in Ω, SobolevSpace.minimalSlope μ hQ H.val x ∂μ) ^ 2 ≤
        P * μ.real Ω * balancedGradientConstant d q := by
  let ν := μ.restrict Ω
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hfin.lt_top⟩
  let U := fun x => SobolevSpace.toLp μ hQ H.val x
  let G := fun x => SobolevSpace.minimalSlope μ hQ H.val x
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hd : 0 < d := hq0.trans hqd
  have hα : 0 < q - 1 := sub_pos.mpr hq
  have hU0 : 0 ≤ᵐ[ν] U := ae_restrict_of_ae hH
  have hUm : AEMeasurable U ν := (Lp.stronglyMeasurable _).measurable.aemeasurable
  have hV : ν.real univ = μ.real Ω := by simp only [ν, measureReal_restrict_apply_univ]
  have htail (t : ℝ) (ht : 1 ≤ t) :
      ν {x | t ≤ U x} ≤ ENNReal.ofReal (μ.real Ω * t ^ (-d)) := by
    have hb := dirichlet_positive_source_tail μ hQ Ω hfin H hH hd hC hP hsob
      hsource (zero_lt_one.trans_le ht)
    exact hb.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hbalance (Real.rpow_nonneg (by linarith) _)))
  have hUi := integrable_rpow_of_power_tail ν hUm hU0 hq0 hqd measureReal_nonneg htail
  have hUb := integral_rpow_le_of_power_tail ν hUm hU0 hq0 hqd measureReal_nonneg htail
  have hshift := shifted_moment_le ν hUm hU0 hq0.le hUi
  let w := fun x => (1 + U x) ^ q
  have hwpos : ∀ᵐ x ∂ν, 0 < w x := by
    filter_upwards [hU0] with x hx
    exact Real.rpow_pos_of_pos (by change 0 ≤ U x at hx; linarith) _
  have hwm : AEMeasurable w ν := (hUm.const_add 1).pow_const q
  have hGm : AEMeasurable G ν := (Lp.stronglyMeasurable _).measurable.aemeasurable
  have hEe := positive_source_weighted_energy μ hQ Ω H hH P hsource hα
  have hqi : 1 + (q - 1) = q := by ring
  simp only [hqi] at hEe
  have hEg : Integrable (fun x => G x ^ 2 / w x) μ := hEe.1
  have hEn : ∀ᵐ x ∂μ, 0 ≤ G x ^ 2 / w x := by
    filter_upwards [hH] with x hx
    exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) q)
  have hEl : (∫ x, G x ^ 2 / w x ∂ν) ≤ P / (q - 1) :=
    (setIntegral_le_integral hEg hEn).trans hEe.2
  have hcs := integral_sq_le_reciprocal_weight ν hGm hwm hwpos hshift.1 hEg.integrableOn
  let L := 2 ^ q * (1 + q * (q⁻¹ + (d - q)⁻¹))
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hMb : (∫ x, w x ∂ν) ≤ μ.real Ω * L := by
    apply hshift.2.trans
    have hh := mul_le_mul_of_nonneg_left (add_le_add (le_refl (ν.real univ)) hUb)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q)
    rw [hV]
    rw [hV] at hh
    exact hh.trans_eq (by dsimp only [L]; ring)
  refine ⟨hcs.1, ?_⟩
  calc
    _ ≤ (P / (q - 1)) * (μ.real Ω * L) := hcs.2.trans
      (mul_le_mul hEl hMb (integral_nonneg_of_ae (hwpos.mono fun _ hx => hx.le))
        (div_nonneg hP hα.le))
    _ = _ := by dsimp only [L, balancedGradientConstant]; ring

end RegularPointCoordinates

end

end OAI
