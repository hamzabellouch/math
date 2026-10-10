import OAI.Geometry.RCD.Coordinates.RegularMassSmallness

namespace OAI

/-! # Smallness in the inverse mean metric of the actual patch operators -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

/-- The original pinching radius is a fixed multiple of the mean radius. -/
def pinchingMassUnitFactor (n : ℕ) : ℝ := (16384 : ℝ) ^ 2 / (16384 : ℝ) ^ n

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual conjugated full mass is small in its own inverse mean
metric, with no lower eigenvalue bound or discarded singular part. -/
theorem regular_pinching_mass_small {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1) (hCχ : 0 ≤ Cχ)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 2)
    (i : ℕ) (xi : Euclidean n) :
    let r := e.heat.radius / (2 : ℝ) ^ (i + 15)
    ⟪xi, e.heat.pinchingMassMatrix q hq i xi⟫_ℝ ≤
      pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
        (zeta + |K| * r ^ 2) * ⟪xi, (e.heat.meanAt q hq (i + 15)).symm xi⟫_ℝ := by
  intro r
  let s := distanceSourceRadius e.heat.radius i
  let R := e.heat.meanAt q hq (i + 15)
  have hr : 0 < r := div_pos e.heat.radius_pos (by positivity)
  have hs : s = 16384 * r := by
    dsimp only [s, r, distanceSourceRadius]
    rw [show i + 15 = (i + 1) + 14 by omega, pow_add]
    norm_num
    ring
  have hscale : s ^ 2 / s ^ n = pinchingMassUnitFactor n * (r ^ 2 / r ^ n) := by
    rw [hs, mul_pow, mul_pow]
    dsimp only [pinchingMassUnitFactor]
    ring
  have hball : s / 49152 = r / 3 := by rw [hs]; ring
  have hR : ⟪R.symm xi, e.heat.meanAt q hq (i + 15) (R.symm xi)⟫_ℝ =
      ⟪xi, R.symm xi⟫_ℝ := by
    change ⟪R.symm xi, R (R.symm xi)⟫_ℝ = _
    rw [R.apply_symm_apply, real_inner_comm]
  have hb := regular_local_mass_small hX e hq hzeta hzeta1 hCχ hsmall i (R.symm xi)
  have hf : 0 ≤ pinchingMassUnitFactor n := by dsimp only [pinchingMassUnitFactor]; positivity
  change ⟪xi, frozenConjugate R ((s ^ 2 / s ^ n) •
    e.heat.mass.massOperator (ball q (s / 49152))) xi⟫_ℝ ≤ _
  rw [inner_frozenConjugate, smul_apply, inner_smul_right, hball, hscale]
  calc
    _ = pinchingMassUnitFactor n * ((r ^ 2 / r ^ n) *
        ⟪R.symm xi, e.heat.mass.massOperator (ball q (r / 3)) (R.symm xi)⟫_ℝ) := by ring
    _ ≤ pinchingMassUnitFactor n * (regularSmallMassCoefficient n Cχ *
        (zeta + |K| * r ^ 2) * ⟪R.symm xi, e.heat.meanAt q hq (i + 15) (R.symm xi)⟫_ℝ) :=
      mul_le_mul_of_nonneg_left hb hf
    _ = _ := by rw [hR]; ring

end RegularPointCoordinates

end

end OAI
