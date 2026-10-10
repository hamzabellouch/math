import OAI.Geometry.RCD.Sobolev.MeasuredRadialCutoff
import OAI.Geometry.RCD.Sobolev.InteriorBoundedGradientRepresentative

namespace OAI

/-! # The actual Sobolev cutoff at the prescribed physical scale -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem scaled_radial_cutoff_sobolev (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (hQ : QuadraticCheegerEnergy μ) (p : X) {a b r : ℝ} (hab : a<b) (hr : 0<r) :
    ∃ η : SobolevSpace μ hQ,
      SobolevSpace.toLp μ hQ η=ᵐ[μ]
        nestedBallCutoff p (a*r) (b*r) ∧
      (∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ η x≤
        (b*r-a*r)⁻¹) ∧
      ∀ᵐ x ∂μ, r^2*localGamma μ hQ η η x≤((b-a)⁻¹)^2 := by
  have habr : a*r<b*r := mul_lt_mul_of_pos_right hab hr
  have hLip : LipschitzWith ⟨(b*r-a*r)⁻¹,inv_nonneg.mpr (sub_pos.mpr habr).le⟩
      (nestedBallCutoff p (a*r) (b*r)) := nestedBallCutoff_lipschitz p habr
  have hcomp : HasCompactSupport (nestedBallCutoff p (a*r) (b*r)) :=
    nestedBallCutoff_hasCompactSupport p habr
  let η : SobolevSpace μ hQ := SobolevSpace.ofLipschitzCompact μ hQ hLip hcomp
  have hrep : SobolevSpace.toLp μ hQ η=ᵐ[μ] nestedBallCutoff p (a*r) (b*r) :=
    SobolevSpace.ofLipschitzCompact_coe μ hQ hLip hcomp
  have hbound : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ η x≤(b*r-a*r)⁻¹ :=
    SobolevSpace.minimalSlope_le_lipschitz μ hQ η hLip hrep
  refine ⟨η,hrep,hbound,?_⟩
  filter_upwards [hbound,localGamma_self μ hQ η,
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ η)] with x hx he hn
  have hs := pow_le_pow_left₀ hn hx 2
  have hscaled := mul_le_mul_of_nonneg_left hs (sq_nonneg r)
  have hcancel : r^2*((b*r-a*r)⁻¹)^2=((b-a)⁻¹)^2 := by
    field_simp [hr.ne',sub_ne_zero.mpr (ne_of_gt hab)]
  rw [← he,hcancel] at hscaled
  exact hscaled

end RegularPointCoordinates

end

end OAI
