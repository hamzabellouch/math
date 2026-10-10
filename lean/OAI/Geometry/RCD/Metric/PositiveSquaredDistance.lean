import OAI.Geometry.RCD.Metric.InwardDistance
import OAI.Geometry.RCD.Harmonic.LocalConstantHarmonic

namespace OAI

/-! # A compact Sobolev representative of the positive squared distance

Adding a genuine cutoff constant to the inward primitive makes the
boundary datum nonnegative globally and exactly dist²/2 on the working ball.
-/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

def positiveSquaredDistance {p : X} {R C : ℝ} (hR : 0 ≤ R)
    (χ : GoodLaplacianCutoff μ hQ p R C) : SobolevSpace μ hQ :=
  inwardQuadratic μ hQ p hR + (R ^ 2 / 2) • χ.sobolev

def positiveSquaredDistanceValue {p : X} {R C : ℝ}
    (χ : GoodLaplacianCutoff μ hQ p R C) (x : X) : ℝ :=
  (inwardDistance p R x) ^ 2 / 2 - R * inwardDistance p R x + (R ^ 2 / 2) * χ.weight x

theorem positiveSquaredDistance_representative {p : X} {R C : ℝ} (hR : 0 ≤ R)
    (χ : GoodLaplacianCutoff μ hQ p R C) :
    SobolevSpace.toLp μ hQ (positiveSquaredDistance μ hQ hR χ) =ᵐ[μ]
      positiveSquaredDistanceValue μ hQ χ := by
  filter_upwards [inwardQuadratic_coe μ hQ p hR, χ.representative,
    Lp.coeFn_add (SobolevSpace.toLp μ hQ (inwardQuadratic μ hQ p hR))
      ((R ^ 2 / 2) • SobolevSpace.toLp μ hQ χ.sobolev),
    Lp.coeFn_smul (R ^ 2 / 2) (SobolevSpace.toLp μ hQ χ.sobolev)] with x hq hχ ha hs
  change (SobolevSpace.toLp μ hQ (inwardQuadratic μ hQ p hR) +
    (R ^ 2 / 2) • SobolevSpace.toLp μ hQ χ.sobolev) x = _
  simp only [ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul, hq, hχ,
    positiveSquaredDistanceValue]

omit [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
theorem positiveSquaredDistanceValue_on_ball {p : X} {R C : ℝ}
    (χ : GoodLaplacianCutoff μ hQ p R C) {x : X} (hx : x ∈ ball p R) :
    positiveSquaredDistanceValue μ hQ χ x = dist p x ^ 2 / 2 := by
  have hd : dist p x < R := by simpa only [mem_ball, dist_comm] using hx
  simp only [positiveSquaredDistanceValue, inwardDistance, χ.one x hx,
    max_eq_left (sub_nonneg.mpr hd.le)]
  ring

omit [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
theorem positiveSquaredDistanceValue_bounds {p : X} {R C : ℝ} (hR : 0 ≤ R)
    (χ : GoodLaplacianCutoff μ hQ p R C) (x : X) :
    0 ≤ positiveSquaredDistanceValue μ hQ χ x ∧
      positiveSquaredDistanceValue μ hQ χ x ≤ R ^ 2 / 2 := by
  by_cases hx : x ∈ ball p R
  · rw [positiveSquaredDistanceValue_on_ball μ hQ χ hx]
    have hd : dist p x < R := by simpa only [mem_ball, dist_comm] using hx
    constructor
    · positivity
    · nlinarith [dist_nonneg (x := p) (y := x)]
  · have hd : R ≤ dist p x := by simpa only [mem_ball, dist_comm, not_lt] using hx
    simp only [positiveSquaredDistanceValue, inwardDistance, max_eq_right (sub_nonpos.mpr hd),
      zero_pow (by norm_num : 2 ≠ 0), zero_div, mul_zero, sub_zero, zero_add]
    exact ⟨mul_nonneg (by positivity) (χ.bounds x).1,
      by nlinarith [(χ.bounds x).2, sq_nonneg R]⟩

omit [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
theorem positiveSquaredDistanceValue_lipschitz {p : X} {R C : ℝ} (hR : 0 ≤ R)
    (χ : GoodLaplacianCutoff μ hQ p R C) :
    ∃ L : ℝ≥0, LipschitzWith L (positiveSquaredDistanceValue μ hQ χ) := by
  let k : ℝ := (C / R).toNNReal
  let L : ℝ≥0 := ⟨R + (R ^ 2 / 2) * k, by dsimp only [k]; positivity⟩
  refine ⟨L, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  let a := inwardDistance p R x
  let b := inwardDistance p R y
  have ha : 0 ≤ a ∧ a ≤ R := ⟨le_max_right _ _, max_le (by linarith [dist_nonneg (x := p) (y := x)]) hR⟩
  have hb : 0 ≤ b ∧ b ≤ R := ⟨le_max_right _ _, max_le (by linarith [dist_nonneg (x := p) (y := y)]) hR⟩
  have hab : |a - b| ≤ dist x y := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (inwardDistance_lipschitz p R).dist_le_mul x y
  have hf : |(a + b) / 2 - R| ≤ R := (abs_le).mpr ⟨by linarith, by linarith⟩
  have hprimitive : |(a ^ 2 / 2 - R * a) - (b ^ 2 / 2 - R * b)| ≤ R * dist x y := by
    rw [show (a ^ 2 / 2 - R * a) - (b ^ 2 / 2 - R * b) =
      (a - b) * ((a + b) / 2 - R) by ring, abs_mul]
    exact (mul_le_mul hab hf (abs_nonneg _) (dist_nonneg)).trans_eq (mul_comm _ _)
  have hcut : |χ.weight x - χ.weight y| ≤ k * dist x y := by
    simpa only [Real.dist_eq] using χ.lipschitz.dist_le_mul x y
  have he : positiveSquaredDistanceValue μ hQ χ x - positiveSquaredDistanceValue μ hQ χ y =
      ((a ^ 2 / 2 - R * a) - (b ^ 2 / 2 - R * b)) +
        (R ^ 2 / 2) * (χ.weight x - χ.weight y) := by
    dsimp only [positiveSquaredDistanceValue, a, b]
    ring
  rw [Real.dist_eq, he]
  calc
    _ ≤ |(a ^ 2 / 2 - R * a) - (b ^ 2 / 2 - R * b)| +
        |(R ^ 2 / 2) * (χ.weight x - χ.weight y)| := abs_add_le _ _
    _ ≤ R * dist x y + (R ^ 2 / 2) * (k * dist x y) := by
      apply add_le_add hprimitive
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ R ^ 2 / 2)]
      exact mul_le_mul_of_nonneg_left hcut (by positivity)
    _ = (L : ℝ) * dist x y := by
      change _ = (R + R ^ 2 / 2 * k) * dist x y
      ring

/-- The cutoff constant has zero local gradient. The exact distance
chain rule is retained against every Sobolev test direction. -/
theorem positiveSquaredDistance_gamma {p : X} {R C : ℝ} (hR : 0 ≤ R)
    (χ : GoodLaplacianCutoff μ hQ p R C) (a : SobolevSpace μ hQ) :
    ∀ᵐ x ∂μ.restrict (ball p R),
      localGamma μ hQ (positiveSquaredDistance μ hQ hR χ) a x =
        -dist p x * localGamma μ hQ (inwardSobolev μ hQ p R) a x := by
  let w := inwardSobolev μ hQ p R
  have hb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ (⟨R, hR⟩ : ℝ≥0) := by
    filter_upwards [inwardSobolev_bounds μ hQ p hR] with x hx
    exact (abs_of_nonneg hx.1).symm ▸ hx.2
  filter_upwards [ae_restrict_of_ae (localGamma_add_left μ hQ
      (inwardQuadratic μ hQ p hR) ((R ^ 2 / 2) • χ.sobolev) a),
    ae_restrict_of_ae (localGamma_smul_left μ hQ (R ^ 2 / 2) χ.sobolev a),
    ae_restrict_of_ae (localGamma_zero_on_level μ hQ χ.sobolev a 1),
    ae_restrict_of_ae χ.representative,
    ae_restrict_of_ae (localGamma_sub_left μ hQ
      ((1 / 2 : ℝ) • SobolevSpace.square μ hQ w ⟨R, hR⟩) (R • w) a),
    ae_restrict_of_ae (localGamma_smul_left μ hQ (1 / 2 : ℝ)
      (SobolevSpace.square μ hQ w ⟨R, hR⟩) a),
    ae_restrict_of_ae (localGamma_smul_left μ hQ R w a),
    ae_restrict_of_ae (localGamma_square μ hQ w a ⟨R, hR⟩ hb),
    ae_restrict_of_ae (inwardSobolev_coe μ hQ p R), ae_restrict_mem measurableSet_ball]
    with x hadd hsmul hzero hrep hsub hhalf hRmul hsq hw hx
  have hχ : localGamma μ hQ χ.sobolev a x = 0 := hzero (hrep.trans (χ.one x hx))
  have hd : dist p x < R := by simpa only [mem_ball, dist_comm] using hx
  change SobolevSpace.toLp μ hQ w x = _ at hw
  have hw' : SobolevSpace.toLp μ hQ w x = R - dist p x := by
    simpa only [inwardDistance, max_eq_left (sub_nonneg.mpr hd.le)] using hw
  change localGamma μ hQ
    (inwardQuadratic μ hQ p hR + (R ^ 2 / 2) • χ.sobolev) a x = _
  rw [hadd, hsmul, hχ, mul_zero, add_zero]
  change localGamma μ hQ ((1 / 2 : ℝ) • SobolevSpace.square μ hQ w ⟨R, hR⟩ - R • w) a x = _
  rw [hsub, hhalf, hRmul, hsq, hw']
  ring

theorem positiveSquaredDistance_gradient {p : X} {R C : ℝ} (hR : 0 ≤ R)
    (χ : GoodLaplacianCutoff μ hQ p R C)
    (heik : ∀ᵐ x ∂μ.restrict (ball p R),
      localGamma μ hQ (inwardSobolev μ hQ p R) (inwardSobolev μ hQ p R) x = 1) :
    ∀ᵐ x ∂μ.restrict (ball p R),
      localGamma μ hQ (positiveSquaredDistance μ hQ hR χ)
        (positiveSquaredDistance μ hQ hR χ) x = dist p x ^ 2 := by
  filter_upwards [positiveSquaredDistance_gamma μ hQ hR χ
      (positiveSquaredDistance μ hQ hR χ),
    positiveSquaredDistance_gamma μ hQ hR χ (inwardSobolev μ hQ p R), heik,
    ae_restrict_of_ae (localGamma_comm μ hQ (inwardSobolev μ hQ p R)
      (positiveSquaredDistance μ hQ hR χ))] with x hq hw he hc
  rw [hq, hc, hw, he]
  ring

end RegularPointCoordinates

end

end OAI
