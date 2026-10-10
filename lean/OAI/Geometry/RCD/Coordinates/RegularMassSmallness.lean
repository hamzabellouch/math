import OAI.Geometry.RCD.Coordinates.RegularMassMatrices
import OAI.Geometry.RCD.Coordinates.RegularFrameGeometry

namespace OAI

/-! # Smallness of the actual full mass at the pinching radius -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

/-- All volume and cutoff losses in the local smallness estimate. -/
def regularSmallMassCoefficient (n : ℕ) (C : ℝ) : ℝ :=
  (5 / 2 : ℝ) * euclideanUnitVolume n * (8 : ℝ) ^ n *
    (2 * C * (n : ℝ) ^ 2 + (n : ℝ) ^ 2 + 1)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The local Bochner cutoff calculation makes the full original mass
small in its own mean metric. Its coefficient tends to zero with the
splitting error and the rescaled curvature. -/
theorem regular_local_mass_small {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1) (hCχ : 0 ≤ Cχ)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 2)
    (i : ℕ) (v : Euclidean n) :
    let r := e.heat.radius / (2 : ℝ) ^ (i + 15)
    (r ^ 2 / r ^ n) * ⟪v, e.heat.mass.massOperator (ball q (r / 3)) v⟫_ℝ ≤
      regularSmallMassCoefficient n Cχ * (zeta + |K| * r ^ 2) *
        ⟪v, e.heat.meanAt q hq (i + 15) v⟫_ℝ := by
  intro r
  let μ := hausdorff n X
  have homega : 0 < euclideanUnitVolume n := euclideanUnitVolume_pos n
  let U := sobolevColumnMap μ hX.quadratic e.heat.coordinates
  let : IsFiniteMeasureOnCompacts μ := ⟨fun {_s} hs => hX.finiteOnBounded _ hs.isBounded⟩
  have hr : 0 < r := div_pos e.heat.radius_pos (by positivity)
  have hrR : r ≤ e.heat.radius := div_le_self e.heat.radius_pos.le (one_le_pow₀ (by norm_num))
  have houter : e.heat.radius / (2 : ℝ) ^ (i + 12) = 8 * r := by
    dsimp only [r]
    rw [show i + 15 = (i + 12) + 3 by omega, pow_add]
    norm_num
    ring
  have hcutrad : distanceSourceRadius e.heat.radius (i + 9) / 64 = r / 2 := by
    dsimp only [distanceSourceRadius, r]
    simp only [pow_succ]
    ring
  obtain ⟨_S, _T, _hsum, _hbudget, _hgrad, hcuts⟩ := e.poisson q hq
  let χ : GoodLaplacianCutoff μ hX.quadratic q (r / 2) Cχ :=
    hcutrad ▸ Classical.choice (hcuts (i + 9))
  have hsub : ball q (2 * r) ⊆ ball base (2 * (4 * e.heat.radius)) := by
    intro x hx
    have hd := dist_triangle x q base
    have hxq : dist x q < 2 * r := hx
    have hqb : dist q base < e.heat.radius / 32 := hq
    change dist x base < 2 * (4 * e.heat.radius)
    linarith [e.heat.radius_pos]
  let G := fun w => (e.heat.energy w).restrict μ hX.quadratic hsub
  have hvol := e.volume q hq (8 * r) (by positivity) (by
    rw [← houter]
    have hh := div_le_self e.heat.radius_pos.le
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ (i + 12))
    linarith [e.heat.radius_pos])
  have hv := quarter_volume_bounds (by positivity : 0 < 8 * r) (euclideanUnitVolume_pos n) hvol
  have hfirst := e.heat.frameAt_splitting q hq (i + 12)
  have hexact := e.heat.frameAt_exact q hq (i + 12)
  rw [houter] at hfirst hexact
  have hb := original_gram_bochner_mass_le μ hX.quadratic e.heat.coordinates e.heat.mass
    G (e.heat.frameAt q hq (i + 12)) hfirst hexact hr hzeta hCχ (abs_nonneg K) hv.1 χ v
  have hroom : dist q q + (1 / 8 : ℝ) * (e.heat.radius / (2 : ℝ) ^ (i + 12)) ≤
      e.heat.radius / (2 : ℝ) ^ (i + 12) := by rw [dist_self, houter]; linarith
  have hmean := (regular_subball_mean_comparison hX e hq hq hzeta (i + 12)
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num) hroom v).1
  rw [houter, show (1 / 8 : ℝ) * (8 * r) = r by ring] at hmean
  have hg0 := (sobolevMeanGram_isPositive μ hX.quadratic U (ball q (8 * r)) measurableSet_ball).inner_nonneg_right v
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hg0
  have hmean' : ⟪v, sobolevMeanGram μ hX.quadratic U (ball q (8 * r)) measurableSet_ball v⟫_ℝ ≤
      2 * ⟪v, sobolevMeanGram μ hX.quadratic U (ball q r) measurableSet_ball v⟫_ℝ := by
    nlinarith
  have hg1 := (sobolevMeanGram_isPositive μ hX.quadratic U (ball q r) measurableSet_ball).inner_nonneg_right v
  have hm : ⟪v, e.heat.mass.massOperator (ball q (r / 3)) v⟫_ℝ ≤
      ⟪v, e.heat.mass.massOperator (ball q (r / 2)) v⟫_ℝ := by
    rw [← e.heat.mass.measure_real v _ measurableSet_ball,
      ← e.heat.mass.measure_real v _ measurableSet_ball]
    exact measureReal_mono (ball_subset_ball (by linarith)) (measure_ne_top _ _)
  let beta := 2 * Cχ * (n : ℝ) ^ 2 * zeta + |K| * r ^ 2 * ((n : ℝ) ^ 2 * zeta + 1)
  have hbeta : 0 ≤ beta := by dsimp only [beta]; positivity
  have hb' : (r ^ 2 / μ.real (ball q (8 * r))) *
      ⟪v, e.heat.mass.massOperator (ball q (r / 3)) v⟫_ℝ ≤
      beta * (2 * ⟪v, sobolevMeanGram μ hX.quadratic U (ball q r) measurableSet_ball v⟫_ℝ) :=
    (mul_le_mul_of_nonneg_left hm (by positivity)).trans
      (hb.trans (mul_le_mul_of_nonneg_left hmean' hbeta))
  have hratio : μ.real (ball q (8 * r)) / r ^ n ≤ (5 / 4 : ℝ) * euclideanUnitVolume n * (8 : ℝ) ^ n := by
    apply (div_le_iff₀ (pow_pos hr n)).mpr
    simpa only [mul_pow, mul_assoc] using hv.2.2
  have hbeta' : beta ≤ (2 * Cχ * (n : ℝ) ^ 2 + (n : ℝ) ^ 2 + 1) * (zeta + |K| * r ^ 2) := by
    have hn := mul_le_mul_of_nonneg_left hzeta1 (sq_nonneg (n : ℝ))
    have hm := mul_le_mul_of_nonneg_left hn (mul_nonneg (abs_nonneg K) (sq_nonneg r))
    dsimp only [beta]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCχ)
      (sq_nonneg (n : ℝ))) (mul_nonneg (abs_nonneg K) (sq_nonneg r)),
      mul_nonneg (sq_nonneg (n : ℝ)) hzeta]
  have hidentity : (r ^ 2 / r ^ n) * ⟪v, e.heat.mass.massOperator (ball q (r / 3)) v⟫_ℝ =
      (μ.real (ball q (8 * r)) / r ^ n) *
        ((r ^ 2 / μ.real (ball q (8 * r))) * ⟪v, e.heat.mass.massOperator (ball q (r / 3)) v⟫_ℝ) := by
    have hvpos : 0 < μ.real (ball q (8 * r)) := hv.1
    generalize μ.real (ball q (8 * r)) = V at hvpos ⊢
    field_simp [hr.ne', hvpos.ne']
  rw [hidentity]
  change _ ≤ regularSmallMassCoefficient n Cχ * (zeta + |K| * r ^ 2) *
    ⟪v, (e.heat.meanAt q hq (i + 15)).toContinuousLinearMap v⟫_ℝ
  rw [e.heat.meanAt_toContinuousLinearMap]
  calc
    _ ≤ (μ.real (ball q (8 * r)) / r ^ n) *
        (beta * (2 * ⟪v, sobolevMeanGram μ hX.quadratic U (ball q r) measurableSet_ball v⟫_ℝ)) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ ≤ ((5 / 4 : ℝ) * euclideanUnitVolume n * (8 : ℝ) ^ n) *
        (beta * (2 * ⟪v, sobolevMeanGram μ hX.quadratic U (ball q r) measurableSet_ball v⟫_ℝ)) :=
      mul_le_mul_of_nonneg_right hratio (mul_nonneg hbeta (mul_nonneg (by norm_num) hg1))
    _ ≤ ((5 / 4 : ℝ) * euclideanUnitVolume n * (8 : ℝ) ^ n) *
        (((2 * Cχ * (n : ℝ) ^ 2 + (n : ℝ) ^ 2 + 1) * (zeta + |K| * r ^ 2)) *
          (2 * ⟪v, sobolevMeanGram μ hX.quadratic U (ball q r) measurableSet_ball v⟫_ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbeta' (mul_nonneg (by norm_num) hg1))
        (by positivity)
    _ = _ := by dsimp only [regularSmallMassCoefficient, r, U, μ]; ring

end RegularPointCoordinates

end

end OAI
