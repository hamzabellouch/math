import OAI.Geometry.RCD.Coordinates.RegularCenterRadialData
import OAI.Geometry.RCD.Harmonic.RadialLinearCoefficient
import OAI.Geometry.RCD.Harmonic.RadialLinearRepresentatives
import OAI.Geometry.RCD.Sobolev.RadialCutoffChange

namespace OAI

/-! # The actual radial estimates for every covector simultaneously -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Linear assembly keeps the same radial representatives and coefficients
in both the value and gradient bounds. It also gives the near-identity
bound for the covector operator used in the two-center commutator. -/
theorem regular_linear_radial_data {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {p q : X} {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    {a κ B J C A Cχ enlargement zeta eta Cg D Ca : ℝ}
    (e : RegularProjectionEnvironment hX p hk a κ B J C A Cχ enlargement zeta eta)
    (hq : q ∈ ball p (e.heat.radius / 32))
    (d : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca q)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hCχ : 0 ≤ Cχ) (hzeta : 0 ≤ zeta) (i : ℕ) :
    let μ := hausdorff n X
    let s := distanceSourceRadius e.heat.radius i
    let r := s / 64
    let E := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant n Cχ * zeta)
      (normalizedPoissonDefect μ hX.quadratic d.source) i
    let Cv := 2 * D ^ 2 + 8192 * ((n : ℝ) * 2) ^ 2 * B *
      ((4 / (3 * euclideanUnitVolume n)) * (64 : ℝ) ^ n)
    let Ce := radialEnergyConstant K n Cg 1 A B J Cχ *
      ((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹ * D ^ 2 +
        (4 / (3 * euclideanUnitVolume n)) * (128 : ℝ) ^ n)
    ∃ (coeff : Euclidean n →L[ℝ] Euclidean n)
      (G : Euclidean n →L[ℝ] SobolevSpace μ hX.quadratic),
      ‖(d.frame i).symm.toContinuousLinearMap.comp coeff - ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤
        (n : ℝ) ^ 4 * Real.sqrt (2 * Ca ^ 2 * (D ^ 2 * E + radialFitQualitativeConstant n Cχ * zeta)) ∧
      ∀ b : Euclidean n,
        (SobolevSpace.toLp μ hX.quadratic (G b) =ᵐ[μ.restrict (ball q r)]
          localGamma μ hX.quadratic (d.replacement.replacement i)
            (sobolevColumnMap μ hX.quadratic e.heat.coordinates (d.frame i b))) ∧
        let R := G b - centeredAffineSobolev μ hX.quadratic e.heat.coordinates
          e.one.sobolev (e.heat.values q) (coeff b)
        ‖normalizeLocalL2 μ (ball q r) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp μ hX.quadratic (ball q r) R)‖ ^ 2 ≤
            (n : ℝ) ^ 2 * (Cv * r ^ 2 * E) * ‖b‖ ^ 2 ∧
        (μ.real (ball q (r / 2)))⁻¹ *
          (∫ x in ball q (r / 2), localGamma μ hX.quadratic R R x ∂μ) ≤
            (n : ℝ) ^ 2 * Ce * E * ‖b‖ ^ 2 := by
  dsimp only
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := distanceSourceRadius e.heat.radius i
  let r := s / 64
  let E := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant n Cχ * zeta)
    (normalizedPoissonDefect μ hQ d.source) i
  let Cv := 2 * D ^ 2 + 8192 * ((n : ℝ) * 2) ^ 2 * B *
    ((4 / (3 * euclideanUnitVolume n)) * (64 : ℝ) ^ n)
  let Ce := radialEnergyConstant K n Cg 1 A B J Cχ *
    ((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹ * D ^ 2 +
      (4 / (3 * euclideanUnitVolume n)) * (128 : ℝ) ^ n)
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hr : 0 < r := by dsimp only [r]; positivity
  have hsR : s ≤ e.heat.radius := by
    have hh := distanceSourceRadius_outer_le e.heat.radius_pos.le i
    change 2 * s ≤ e.heat.radius at hh
    linarith
  have hE : 0 ≤ E := (radial_fit_pinching_envelope_budget d.source hκ hCχ hzeta d.summable).2.2 i |>.1
  have hCv : 0 ≤ Cv := by dsimp only [Cv]; have := euclideanUnitVolume_pos n; positivity
  have hvol : 0 < μ.real (ball q (r / 2)) :=
    (quarter_volume_bounds (by positivity) (euclideanUnitVolume_pos n)
      (e.volume q hq (r / 2) (by positivity) (by dsimp only [r]; linarith))).1
  obtain ⟨c, g, hmatrix, hrows⟩ := d.rows i
  refine ⟨finiteCoefficientMap c, sobolevColumnMap μ hQ g, ?_, ?_⟩
  · have hh := finiteCoefficientMap_relative_bound (d.frame i) c
      (by positivity : 0 ≤ (n : ℝ) ^ 2 * Real.sqrt
        (2 * Ca ^ 2 * (D ^ 2 * E + radialFitQualitativeConstant n Cχ * zeta))) hmatrix
    convert hh using 1
    ring
  · intro b
    have hf := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by dsimp only [r]; linarith : r ≤ s / 4))
      (d.gradient i q (by simp only [dist_self]; positivity))
    have hrep := localRadialDerivative_column μ hQ (ball q r) (d.replacement.replacement i)
      hf (transformedColumn μ hQ e.heat.coordinates (d.frame i)) g (fun j => (hrows j).1) b
    have hradial := localRadialDerivative_representative μ hQ (ball q r) (d.replacement.replacement i)
      (sobolevColumnMap μ hQ (transformedColumn μ hQ e.heat.coordinates (d.frame i)) b) hf
    rw [hrep] at hradial
    have hrep' := (SobolevSpace.restrictLp_coe μ hQ (ball q r) (sobolevColumnMap μ hQ g b)).symm.trans
      hradial
    rw [sobolevColumnMap_transformed, ContinuousLinearMap.comp_apply] at hrep'
    refine ⟨hrep', ?_⟩
    have he (j : Fin n) : (∫ x in ball q (r / 2), localGamma μ hQ
        (g j - centeredAffineSobolev μ hQ e.heat.coordinates (d.cutoff i).sobolev (e.heat.values q) (c j))
        (g j - centeredAffineSobolev μ hQ e.heat.coordinates (d.cutoff i).sobolev (e.heat.values q) (c j)) x ∂μ) ≤
        μ.real (ball q (r / 2)) * (Ce * E) := by
      exact (inv_mul_le_iff₀ hvol).mp (hrows j).2.2
    have hh := linear_centered_radial_bounds μ hQ e.heat.coordinates g (d.cutoff i).sobolev
      (e.heat.values q) c (ball q r) (ball q (r / 2))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (mul_nonneg (mul_nonneg hCv (sq_nonneg r)) hE)
      (fun j => (hrows j).2.1) he b
    have hone := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by dsimp only [r]; linarith : r ≤ 2 * s)) (e.oneRepresentative q hq i)
    have hchi : SobolevSpace.toLp μ hQ (d.cutoff i).sobolev =ᵐ[μ.restrict (ball q r)]
        fun _ => (1 : ℝ) := by
      filter_upwards [ae_restrict_of_ae (d.cutoff i).representative, ae_restrict_mem measurableSet_ball]
        with x hx hball
      exact hx.trans ((d.cutoff i).one x hball)
    have hvchange := centered_radial_cutoff_change μ hQ e.heat.coordinates
      (sobolevColumnMap μ hQ g b) e.one.sobolev (d.cutoff i).sobolev (e.heat.values q)
      (finiteCoefficientMap c b) (ball q r) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hone hchi
    have hsub : ball q (r / 2) ⊆ ball q r := ball_subset_ball (by linarith)
    have hechange := centered_radial_cutoff_change μ hQ e.heat.coordinates
      (sobolevColumnMap μ hQ g b) e.one.sobolev (d.cutoff i).sobolev (e.heat.values q)
      (finiteCoefficientMap c b) (ball q (r / 2)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (ae_restrict_of_ae_restrict_of_subset hsub hone) (ae_restrict_of_ae_restrict_of_subset hsub hchi)
    refine ⟨?_, ?_⟩
    · rw [hvchange.1]
      exact hh.1
    rw [hechange.2]
    change (μ.real (ball q (r / 2)))⁻¹ * _ ≤ (n : ℝ) ^ 2 * Ce * E * ‖b‖ ^ 2
    apply (inv_mul_le_iff₀ hvol).2
    exact hh.2.trans_eq (by ring)

end RegularPointCoordinates

end

end OAI
