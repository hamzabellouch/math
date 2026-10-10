import OAI.Geometry.RCD.Transport.ShortPlanFlux
import OAI.Analysis.RCDHeat.WeightedGradientConvex

namespace OAI

/-! # A finite radial first-variation inequality

The exact quadratic decrement and cost replace a Kantorovich potential.
The error depends only on the short-plan pullback modulus, uniformly in
the chosen transport plan.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
attribute [local instance] pathBorel pathBorelSpace

theorem radial_variation_lower_bound (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    (q g : SobolevSpace μ hQ) {a R A ε η : ℝ}
    (ha : 0 < a) (hR : 0 ≤ R) (hε : 0 < ε) (hη : 0 ≤ η)
    (hlen : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ a * R)
    (hcost : (∫ γ, dist (γ 0) (γ 1) ^ 2 ∂π) = a ^ 2 * A)
    (hdec : (∫ γ, SobolevSpace.toLp μ hQ q (γ 0) -
      SobolevSpace.toLp μ hQ q (γ 1) ∂π) = (a - a ^ 2 / 2) * A)
    (hclose : ∀ t : Time,
      ‖testPlanPullback μ π hC hc t (SobolevSpace.minimalSlope μ hQ (q + ε • g)) -
        testPlanPullback μ π hC hc 0 (SobolevSpace.minimalSlope μ hQ (q + ε • g))‖ ≤ η) :
    ((1 - a / 2) * A -
      (A + weightedGradientSquare μ hQ (π.map (fun γ => γ 0)) (q + ε • g)) / 2 - R * η) / ε ≤
      (∫ γ, SobolevSpace.toLp μ hQ g (γ 1) - SobolevSpace.toLp μ hQ g (γ 0) ∂π) / a := by
  let w := q + ε • g
  let G := SobolevSpace.minimalSlope μ hQ w
  let E := weightedGradientSquare μ hQ (π.map (fun γ => γ 0)) w
  let J := ∫ γ, dist (γ 0) (γ 1) * G (γ 0) ∂π
  have hi (v : SobolevSpace μ hQ) (t : Time) :
      Integrable (fun γ : C(Time, X) => SobolevSpace.toLp μ hQ v (γ t)) π :=
    (compressionPullback_memLp μ π _ (measurable_path_eval t) hC (hc t)
      (SobolevSpace.toLp μ hQ v)).integrable (by norm_num)
  have hrep (t : Time) : ∀ᵐ γ ∂π, SobolevSpace.toLp μ hQ w (γ t) =
      SobolevSpace.toLp μ hQ q (γ t) + ε * SobolevSpace.toLp μ hQ g (γ t) := by
    apply ae_of_ae_map (measurable_path_eval t).aemeasurable
      (p := fun x => SobolevSpace.toLp μ hQ w x =
        SobolevSpace.toLp μ hQ q x + ε * SobolevSpace.toLp μ hQ g x)
    apply (Measure.absolutelyContinuous_of_le_smul (hc t)).ae_le
    have he : SobolevSpace.toLp μ hQ w =
        SobolevSpace.toLp μ hQ q + ε • SobolevSpace.toLp μ hQ g := by simp [w]
    rw [he]
    filter_upwards [Lp.coeFn_add (SobolevSpace.toLp μ hQ q) (ε • SobolevSpace.toLp μ hQ g),
      Lp.coeFn_smul ε (SobolevSpace.toLp μ hQ g)] with x hx hs
    simp only [hx, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul]
  have hpert : (a - a ^ 2 / 2) * A ≤
      ε * (∫ γ, SobolevSpace.toLp μ hQ g (γ 1) - SobolevSpace.toLp μ hQ g (γ 0) ∂π) +
        ∫ γ, |SobolevSpace.toLp μ hQ w (γ 1) - SobolevSpace.toLp μ hQ w (γ 0)| ∂π := by
    have hig : Integrable (fun γ : C(Time, X) => ε *
        (SobolevSpace.toLp μ hQ g (γ 1) - SobolevSpace.toLp μ hQ g (γ 0))) π :=
      ((hi g 1).sub (hi g 0)).const_mul ε
    have hiw : Integrable (fun γ : C(Time, X) =>
        |SobolevSpace.toLp μ hQ w (γ 1) - SobolevSpace.toLp μ hQ w (γ 0)|) π :=
      ((hi w 1).sub (hi w 0)).abs
    rw [← hdec, ← integral_const_mul, ← integral_add hig hiw]
    apply integral_mono_ae ((hi q 0).sub (hi q 1))
      ((((hi g 1).sub (hi g 0)).const_mul ε).add (((hi w 1).sub (hi w 0)).abs))
    filter_upwards [hrep 0, hrep 1] with γ h0 h1
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [h0, h1]
    linarith [neg_le_abs ((SobolevSpace.toLp μ hQ q (γ 1) + ε * SobolevSpace.toLp μ hQ g (γ 1)) -
      (SobolevSpace.toLp μ hQ q (γ 0) + ε * SobolevSpace.toLp μ hQ g (γ 0)))]
  have habs := short_plan_absolute_increment_le μ π hg hC hc hD
    (SobolevSpace.minimalSlope_isRelaxed μ hQ w) (mul_nonneg ha.le hR) hη hlen hclose
  have hiG : MemLp (fun γ : C(Time, X) => G (γ 0)) 2 π :=
    compressionPullback_memLp μ π _ (measurable_path_eval 0) hC (hc 0) G
  have hiD2 := hD.integrable_sq
  have hiG2 := hiG.integrable_sq
  have hEmap : E = ∫ γ : C(Time, X), G (γ 0) ^ 2 ∂π := by
    exact integral_map (measurable_path_eval 0).aemeasurable
      (((Lp.stronglyMeasurable G).pow 2).aestronglyMeasurable)
  have hJ : J ≤ a * (A + E) / 2 := by
    have hh := integral_mono ((hD.integrable_mul hiG).const_mul (2 * a))
      (hiD2.add (hiG2.const_mul (a ^ 2))) (fun γ => show
        2 * a * (dist (γ 0) (γ 1) * G (γ 0)) ≤
          dist (γ 0) (γ 1) ^ 2 + a ^ 2 * G (γ 0) ^ 2 by
        nlinarith only [sq_nonneg (dist (γ 0) (γ 1) - a * G (γ 0))])
    simp only [integral_const_mul, integral_add hiD2 (hiG2.const_mul (a ^ 2)), Pi.add_apply] at hh
    rw [hcost, ← hEmap] at hh
    change 2 * a * J ≤ a ^ 2 * A + a ^ 2 * E at hh
    apply (mul_le_mul_iff_of_pos_left (show 0 < 2 * a by positivity)).mp
    nlinarith
  apply (div_le_div_iff₀ hε ha).mpr
  change ((1 - a / 2) * A - (A + E) / 2 - R * η) * a ≤ _
  change (∫ γ, |SobolevSpace.toLp μ hQ w (γ 1) - SobolevSpace.toLp μ hQ w (γ 0)| ∂π) ≤
    J + a * R * η at habs
  nlinarith

end RegularPointCoordinates

end OAI
