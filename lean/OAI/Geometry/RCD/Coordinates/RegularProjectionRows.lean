import OAI.Geometry.RCD.Coordinates.RegularCenterRadialData
import OAI.Geometry.RCD.Harmonic.CenteredProjectionRows
import OAI.Geometry.RCD.Coordinates.CenteredNormalization

namespace OAI

/-! # Actual radial rows in the coordinates used by sharp projection -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

def projectionRowConstant (n : ℕ) (B D : ℝ) : ℝ :=
  ((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) *
    (2 * D ^ 2 + 8192 * ((n : ℝ) * 2) ^ 2 * B *
      ((4 / (3 * euclideanUnitVolume n)) * (64 : ℝ) ^ n)) / 64 ^ 2

theorem projectionRowConstant_nonneg (n : ℕ) {B D : ℝ} (hB : 0 ≤ B) :
    0 ≤ projectionRowConstant n B D := by
  unfold projectionRowConstant
  have hω := euclideanUnitVolume_pos n
  positivity

/-- The same exact frames and local constant turn the radial rows into
centered projection rows on the smaller ball, with a uniform coefficient. -/
theorem regular_center_projection_rows {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {p q : X} {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    {a κ B J C A Cχ enlargement zeta eta Cg D Ca : ℝ}
    (e : RegularProjectionEnvironment hX p hk a κ B J C A Cχ enlargement zeta eta)
    (hq : q ∈ ball p (e.heat.radius / 32))
    (d : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca q)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hCχ : 0 ≤ Cχ) (hzeta : 0 ≤ zeta) (i : ℕ) :
    let s := distanceSourceRadius e.heat.radius i
    let N := d.frame i
    let uc := centeredColumn (hausdorff n X) hX.quadratic
      (transformedColumn (hausdorff n X) hX.quadratic e.heat.coordinates N)
      ((N : Euclidean n →L[ℝ] Euclidean n).adjoint (e.heat.values q)) e.one.sobolev
    let W := fun x => (N : Euclidean n →L[ℝ] Euclidean n).adjoint (e.heat.values x) -
      (N : Euclidean n →L[ℝ] Euclidean n).adjoint (e.heat.values q)
    let E := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant n Cχ * zeta)
      (normalizedPoissonDefect (hausdorff n X) hX.quadratic d.source) i
    FirstOrderSplittingOn (hausdorff n X) hX.quadratic q (2 * s) zeta uc W ∧
    sobolevMeanGram (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic uc)
      (ball q (2 * s)) measurableSet_ball = ContinuousLinearMap.id ℝ (Euclidean n) ∧
    IsPointedApproximation q 0 (s / 64) 4 zeta (fun x => (s / 64)⁻¹ • W x) ∧
    ∃ (g : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
      (coeff : Fin n → Euclidean n), ∀ j,
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic (g j) =ᵐ[
        (hausdorff n X).restrict (ball q (s / 512))]
        localGamma (hausdorff n X) hX.quadratic (d.replacement.replacement i) (uc j)) ∧
      ‖normalizeLocalL2 (hausdorff n X) (ball q (s / 512))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball q (s / 512))
          (g j - sobolevColumnMap (hausdorff n X) hX.quadratic uc (coeff j)))‖ ^ 2 ≤
        projectionRowConstant n B D * s ^ 2 * E := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := distanceSourceRadius e.heat.radius i
  let N := d.frame i
  let u := e.heat.coordinates
  let z := e.heat.values q
  let E := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant n Cχ * zeta)
    (normalizedPoissonDefect μ hQ d.source) i
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hsR : s ≤ e.heat.radius := by
    have hh := distanceSourceRadius_outer_le e.heat.radius_pos.le i
    dsimp only [s]
    linarith
  have hone := e.oneRepresentative q hq i
  have hsmall : ball q (s / 512) ⊆ ball q (2 * s) := ball_subset_ball (by linarith)
  have honeSmall := ae_restrict_of_ae_restrict_of_subset hsmall hone
  have hfirst := (d.splitting i).center μ hQ
    ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) e.one.sobolev hone
  have hnormal : sobolevMeanGram μ hQ
      (sobolevColumnMap μ hQ (centeredColumn μ hQ (transformedColumn μ hQ u N)
        ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) e.one.sobolev))
      (ball q (2 * s)) measurableSet_ball = ContinuousLinearMap.id ℝ (Euclidean n) := by
    rw [centeredColumn_meanGram μ hQ _ _ measurableSet_ball _ _ hone,
      sobolevColumnMap_transformed]
    exact d.exactFrame i
  refine ⟨hfirst, hnormal, d.metric i, ?_⟩
  obtain ⟨coeff, g, _hmatrix, hrows⟩ := d.rows i
  refine ⟨g, fun j => N.symm (coeff j), ?_⟩
  intro j
  have hrow := hrows j
  have hsub : ball q (s / 512) ⊆ ball q (s / 64) := ball_subset_ball (by linarith)
  have hrep : SobolevSpace.toLp μ hQ (g j) =ᵐ[μ.restrict (ball q (s / 512))]
      localGamma μ hQ (d.replacement.replacement i) (transformedColumn μ hQ u N j) := by
    exact ae_restrict_of_ae_restrict_of_subset hsub hrow.1
  refine ⟨centered_radial_representative μ hQ (transformedColumn μ hQ u N)
    (d.replacement.replacement i) (g j) e.one.sobolev
    ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) _ j honeSmall hrep, ?_⟩
  have hchi : SobolevSpace.toLp μ hQ (d.cutoff i).sobolev =ᵐ[μ.restrict (ball q (s / 512))]
      fun _ => (1 : ℝ) := by
    filter_upwards [ae_restrict_of_ae (d.cutoff i).representative, ae_restrict_mem measurableSet_ball]
      with x hx hball
    exact hx.trans ((d.cutoff i).one x (hsub hball))
  have hE : 0 ≤ E := (radial_fit_pinching_envelope_budget d.source hκ hCχ hzeta d.summable).2.2 i |>.1
  have hvolBig := e.volume q hq (s / 64) (by positivity) (by linarith)
  have hvolSmall := e.volume q hq (s / 512) (by positivity) (by linarith)
  have hVbig : 0 < μ.real (ball q (s / 64)) :=
    (quarter_volume_bounds (by positivity) (euclideanUnitVolume_pos n) hvolBig).1
  have hVsmall : 0 < μ.real (ball q (s / 512)) :=
    (quarter_volume_bounds (by positivity) (euclideanUnitVolume_pos n) hvolSmall).1
  have hratio := radial_fraction_volume_ratio (by positivity : 0 < s / 64)
    (by norm_num : (0 : ℝ) < 1 / 8) (euclideanUnitVolume_pos n) hvolBig
    (by simpa only [show (1 / 8 : ℝ) * (s / 64) = s / 512 by ring] using hvolSmall)
  have hvol : μ.real (ball q (s / 64)) ≤
      ((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * μ.real (ball q (s / 512)) :=
    (div_le_iff₀ hVsmall).mp hratio
  have hω := euclideanUnitVolume_pos n
  have hbound := normalized_centered_frame_fit μ hQ hsub
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hVbig hVsmall
    u (g j) e.one.sobolev (d.cutoff i).sobolev N z (coeff j)
    (by positivity) hvol honeSmall hchi hrow.2.1
  convert hbound using 1
  dsimp only [projectionRowConstant, s]
  ring

end RegularPointCoordinates

end

end OAI
