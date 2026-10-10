import OAI.Geometry.RCD.Sobolev.PositiveSourceMoment
import OAI.Geometry.RCD.Sobolev.PositiveSourceTruncation

namespace OAI

/-!
# Power tails from the actual Dirichlet truncation test

This is the Sobolev step in the positive-source estimate. The measure
bound is derived from clipped moments and then applied to genuine
Dirichlet functions with a bounded positive source functional.
-/

open Set MeasureTheory Filter
open scoped InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

/-- The clipped Sobolev moment inequality implies the weak power tail. -/
theorem power_tail_of_clip_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] {H : X → ℝ} (hH : Measurable H)
    {d C : ℝ} (hd : 0 < d) (hC : 0 ≤ C)
    (hclip : ∀ t : ℝ, 0 < t →
      (∫ x, (positiveClip t (H x)) ^ (2 * d) ∂ν) ^ (1 / d) ≤ C * t)
    {t : ℝ} (ht : 0 < t) :
    ν {x | t ≤ H x} ≤ ENNReal.ofReal (C ^ d * t ^ (-d)) := by
  let S := {x | t ≤ H x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hH
  have hmeas : Measurable (fun x => (positiveClip t (H x)) ^ (2 * d)) :=
    ((positiveClip_lipschitz t).continuous.measurable.comp hH).pow_const _
  have hi : Integrable (fun x => (positiveClip t (H x)) ^ (2 * d)) ν := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable (t ^ (2 * d))
    exact Eventually.of_forall fun x => by
      have h0 : 0 ≤ positiveClip t (H x) := le_min (le_max_right _ _) ht.le
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)]
      exact Real.rpow_le_rpow h0 (min_le_right _ _) (by positivity)
  have hlo : t ^ (2 * d) * ν.real S ≤ ∫ x, (positiveClip t (H x)) ^ (2 * d) ∂ν := by
    have hind : Integrable (S.indicator (fun _ : X => t ^ (2 * d))) ν :=
      (integrable_const _).indicator hS
    have hb := integral_mono_ae hind hi (Eventually.of_forall fun x => by
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        have hxt : t ≤ H x := hx
        have hx0 : 0 ≤ H x := ht.le.trans hxt
        simp only [positiveClip, max_eq_left hx0, min_eq_right hxt]
        exact le_rfl
      · rw [indicator_of_notMem hx]
        exact Real.rpow_nonneg (le_min (le_max_right _ _) ht.le) _)
    simpa only [integral_indicator_const _ hS, smul_eq_mul, mul_comm] using hb
  have hJ : 0 ≤ ∫ x, (positiveClip t (H x)) ^ (2 * d) ∂ν := by
    exact integral_nonneg fun x => Real.rpow_nonneg (le_min (le_max_right _ _) ht.le) _
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hJ (1 / d)) (hclip t ht) hd.le
  rw [one_div, Real.rpow_inv_rpow hJ hd.ne'] at hp
  have hdiv : ν.real S ≤ (C * t) ^ d / t ^ (2 * d) :=
    (le_div_iff₀ (Real.rpow_pos_of_pos ht _)).mpr (by nlinarith [hlo.trans hp])
  have he : (C * t) ^ d / t ^ (2 * d) = C ^ d * t ^ (-d) := by
    rw [Real.mul_rpow hC ht.le, Real.rpow_neg ht.le,
      show 2 * d = d + d by ring, Real.rpow_add ht]
    field_simp
  have hb : ν.real S ≤ C ^ d * t ^ (-d) := hdiv.trans_eq he
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν S)]
  exact ENNReal.ofReal_le_ofReal hb

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The weak power tail for a positive-source Dirichlet solution. The
Sobolev inequality and source bound are stated separately, on the actual
Dirichlet space. The desired tail is derived rather than postulated. -/
theorem dirichlet_positive_source_tail (Ω : Set X) (hΩfin : μ Ω ≠ ∞)
    (H : SobolevSpace.dirichlet μ hQ Ω)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x)
    {d C P : ℝ} (hd : 0 < d) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        C * energyForm μ hQ φ.val φ.val)
    (hsource : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, ∀ s : ℝ, 0 ≤ s →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧ SobolevSpace.toLp μ hQ φ.val x ≤ s) →
      energyForm μ hQ H.val φ.val ≤ P * s)
    {t : ℝ} (ht : 0 < t) :
    (μ.restrict Ω) {x | t ≤ SobolevSpace.toLp μ hQ H.val x} ≤
      ENNReal.ofReal ((C * P) ^ d * t ^ (-d)) := by
  let : IsFiniteMeasure (μ.restrict Ω) := ⟨by simpa using hΩfin.lt_top⟩
  apply power_tail_of_clip_moment (μ.restrict Ω) (Lp.stronglyMeasurable _).measurable hd
    (mul_nonneg hC hP) ?_ ht
  intro s hs
  let T := positiveTruncation μ hQ H.val s hs.le
  let φ : SobolevSpace.dirichlet μ hQ Ω :=
    ⟨T, positiveTruncation_mem_dirichlet μ hQ H.val H.property hs.le⟩
  have he : (∫ x in Ω, (positiveClip s (SobolevSpace.toLp μ hQ H.val x)) ^ (2 * d) ∂μ) =
      ∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (positiveTruncation_coe μ hQ H.val hs.le),
      ae_restrict_of_ae (positiveTruncation_bounds μ hQ H.val hs.le)] with x hx hb
    change (positiveClip s (SobolevSpace.toLp μ hQ H.val x)) ^ (2 * d) =
      |SobolevSpace.toLp μ hQ T x| ^ (2 * d)
    rw [abs_of_nonneg hb.1, hx]
  rw [he]
  have hb := positiveTruncation_energy_le μ hQ Ω H hH P hsource hs.le
  calc
    _ ≤ C * energyForm μ hQ T T := hsob φ
    _ ≤ C * (P * s) := mul_le_mul_of_nonneg_left hb hC
    _ = (C * P) * s := by ring

end RegularPointCoordinates

end

end OAI
