import OAI.Geometry.RCD.Coordinates.RegularLinearRadialData
import OAI.Geometry.RCD.Coordinates.RegularPairFrames
import OAI.Geometry.RCD.Coordinates.CommonFrameRadialFits

namespace OAI

/-! # The actual radial family in a neighboring centered frame -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Both value and gradient estimates transfer together to the common
commutator ball. The added affine constant is the actual coordinate
displacement paired with the transported coefficient. -/
theorem regular_rebased_radial_data {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base first center : X} {a κ B J C A Cχ enlargement zeta eta Cg D Ca : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hfirst : first ∈ ball base (e.heat.radius / 32))
    (hcenter : center ∈ ball base (e.heat.radius / 32))
    (d1 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca first)
    (d2 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca center)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hJ : 0 ≤ J) (hCχ : 0 ≤ Cχ) (hzeta : 0 ≤ zeta)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * (2 : ℝ) ^ n) * zeta) ≤ 1 / 3)
    (i : ℕ) :
    let μ := hausdorff n X
    let s := distanceSourceRadius e.heat.radius i
    let N := d2.frame i
    let U := (centeredSobolevMap μ hX.quadratic e.heat.coordinates e.one.sobolev
      (e.heat.values center)).comp N.toContinuousLinearMap
    let delta := (N : Euclidean n →L[ℝ] Euclidean n).adjoint
      (e.heat.values first - e.heat.values center)
    let Ω := ball center (s / 2048)
    let E := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant n Cχ * zeta)
      (normalizedPoissonDefect μ hX.quadratic d1.source) i
    let Cv := 2 * D ^ 2 + 8192 * ((n : ℝ) * 2) ^ 2 * B *
      ((4 / (3 * euclideanUnitVolume n)) * (64 : ℝ) ^ n)
    let Ce := radialEnergyConstant K n Cg 1 A B J Cχ *
      ((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹ * D ^ 2 +
        (4 / (3 * euclideanUnitVolume n)) * (128 : ℝ) ^ n)
    let Vratio := (5 / 3 : ℝ) * ((1 / 32 : ℝ) ^ n)⁻¹
    let Eratio := (5 / 3 : ℝ) * ((1 / 16 : ℝ) ^ n)⁻¹
    dist first center ≤ s / 512 →
    ∃ (T : Euclidean n →L[ℝ] Euclidean n)
      (G : Euclidean n →L[ℝ] SobolevSpace μ hX.quadratic),
      ‖T - 1‖ ≤ 2 * ((n : ℝ) ^ 4 *
        Real.sqrt (2 * Ca ^ 2 * (D ^ 2 * E + radialFitQualitativeConstant n Cχ * zeta))) ∧
      ∀ b,
        (SobolevSpace.toLp μ hX.quadratic (G b) =ᵐ[μ.restrict Ω]
          localGamma μ hX.quadratic (d1.replacement.replacement i) (U b)) ∧
        let R := G b - U (T b) + ⟪delta, T b⟫_ℝ • e.one.sobolev
        ‖normalizeLocalL2 μ Ω (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp μ hX.quadratic Ω R)‖ ^ 2 ≤
            2 * (Vratio * ((n : ℝ) ^ 2 * (Cv * (s / 64) ^ 2 * E))) * ‖b‖ ^ 2 ∧
        (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hX.quadratic R R x ∂μ) ≤
            2 * (Eratio * ((n : ℝ) ^ 2 * Ce * E)) * ‖b‖ ^ 2 := by
  intro μ s N U delta Ω E Cv Ce Vratio Eratio hroom
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hsR : s ≤ e.heat.radius := by
    have hh := distanceSourceRadius_outer_le e.heat.radius_pos.le i
    change 2 * s ≤ e.heat.radius at hh
    linarith
  have hE : 0 ≤ E := (radial_fit_pinching_envelope_budget d1.source hκ hCχ hzeta d1.summable).2.2 i |>.1
  have hCv : 0 ≤ Cv := by dsimp only [Cv]; have := euclideanUnitVolume_pos n; positivity
  have hCe : 0 ≤ Ce := by
    have hh := (radialEnergyConstant_pos (K := K) (n := n) (G := Cg) (ε := 1) (A := A) hB hJ hCχ).le
    dsimp only [Ce]
    have := euclideanUnitVolume_pos n
    positivity
  have hVratio : 0 ≤ Vratio := by dsimp only [Vratio]; positivity
  have hEratio : 0 ≤ Eratio := by dsimp only [Eratio]; positivity
  have hsubv : Ω ⊆ ball first (s / 64) := by
    apply ball_subset_ball'
    rw [dist_comm center first]
    linarith
  have hsube : Ω ⊆ ball first ((s / 64) / 2) := by
    apply ball_subset_ball'
    rw [dist_comm center first]
    linarith
  have hvol (x : X) (hx : x ∈ ball base (e.heat.radius / 32))
      (t : ℝ) (ht : 0 < t) (hts : t ≤ 2 * e.heat.radius) :
      |μ.real (ball x t) / (euclideanUnitVolume n * t ^ n) - 1| ≤ 1 / 4 := e.volume x hx t ht hts
  have hpos : 0 < μ.real Ω := (quarter_volume_bounds (by positivity)
    (euclideanUnitVolume_pos n) (hvol center hcenter _ (by positivity) (by linarith))).1
  have hposv : 0 < μ.real (ball first (s / 64)) := (quarter_volume_bounds (by positivity)
    (euclideanUnitVolume_pos n) (hvol first hfirst _ (by positivity) (by linarith))).1
  have hpose : 0 < μ.real (ball first ((s / 64) / 2)) := (quarter_volume_bounds (by positivity)
    (euclideanUnitVolume_pos n) (hvol first hfirst _ (by positivity) (by linarith))).1
  have hvr : μ.real (ball first (s / 64)) ≤ Vratio * μ.real Ω := by
    apply (div_le_iff₀ hpos).mp
    exact radial_fraction_volume_ratio (by positivity : 0 < s / 64)
      (by norm_num : (0 : ℝ) < 1 / 32) (euclideanUnitVolume_pos n)
      (hvol first hfirst _ (by positivity) (by linarith))
      (by simpa only [Ω, show (1 / 32 : ℝ) * (s / 64) = s / 2048 by ring] using
        hvol center hcenter (s / 2048) (by positivity) (by linarith))
  have her : μ.real (ball first ((s / 64) / 2)) ≤ Eratio * μ.real Ω := by
    apply (div_le_iff₀ hpos).mp
    exact radial_fraction_volume_ratio (by positivity : 0 < (s / 64) / 2)
      (by norm_num : (0 : ℝ) < 1 / 16) (euclideanUnitVolume_pos n)
      (hvol first hfirst _ (by positivity) (by linarith))
      (by simpa only [Ω, show (1 / 16 : ℝ) * ((s / 64) / 2) = s / 2048 by ring] using
        hvol center hcenter (s / 2048) (by positivity) (by linarith))
  obtain ⟨Craw, Graw, hCraw, hraw⟩ := regular_linear_radial_data hX e hfirst d1 hκ hB hCχ hzeta i
  let M := d1.frame i
  let P := M.symm.toContinuousLinearMap.comp N.toContinuousLinearMap
  let T := rebasedRadialOperator N M Craw
  let G := Graw.comp P
  have hframes := regular_pair_frame_bounds hX e hfirst hcenter d1 d2 hzeta hsmall i (by linarith)
  have hP : ‖P‖ ≤ Real.sqrt 2 := hframes.1
  have hP2 : ‖P‖ ^ 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), norm_nonneg P]
  refine ⟨T, G, rebased_radial_operator_bound_two N M Craw hframes.2 hframes.1 hCraw, ?_⟩
  have hone := ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (by linarith : s / 2048 ≤ 2 * s)) (e.oneRepresentative center hcenter i)
  have hidentity (b : Euclidean n) : ⟪delta, T b⟫_ℝ =
      ⟪e.heat.values first - e.heat.values center, Craw (P b)⟫_ℝ := by
    dsimp only [delta]
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [T, rebasedRadialOperator, P, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  intro b
  have hrep := common_frame_radial_representative μ hX.quadratic Ω (d1.replacement.replacement i)
    e.heat.coordinates e.one.sobolev (e.heat.values center) N M Graw hone
    (fun v => ae_restrict_of_ae_restrict_of_subset hsubv (hraw v).1) b
  refine ⟨hrep, ?_⟩
  have hb := common_frame_radial_bounds μ hX.quadratic e.heat.coordinates e.one.sobolev
    Graw (e.heat.values first) (e.heat.values center) N M Craw hsubv hsube
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hposv hpose hpos
    (mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hCv (sq_nonneg _)) hE))
    (mul_nonneg (mul_nonneg (sq_nonneg _) hCe) hE) hvr her
    (fun v => (hraw v).2.1) (fun v => (hraw v).2.2) b
  have heq : G b - U (T b) + ⟪delta, T b⟫_ℝ • e.one.sobolev =
      Graw (M.symm (N b)) - U (T b) -
        ⟪e.heat.values center - e.heat.values first, Craw (M.symm (N b))⟫_ℝ • e.one.sobolev := by
    rw [hidentity]
    simp only [G, P, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      inner_sub_left, sub_smul]
    module
  rw [heq]
  dsimp only at hb
  constructor
  · apply hb.1.trans
    change Vratio * (((n : ℝ) ^ 2 * (Cv * (s / 64) ^ 2 * E)) * ‖P‖ ^ 2) * ‖b‖ ^ 2 ≤ _
    calc
      _ ≤ Vratio * (((n : ℝ) ^ 2 * (Cv * (s / 64) ^ 2 * E)) * 2) * ‖b‖ ^ 2 := by gcongr
      _ = _ := by ring
  · apply hb.2.trans
    change Eratio * (((n : ℝ) ^ 2 * Ce * E) * ‖P‖ ^ 2) * ‖b‖ ^ 2 ≤ _
    calc
      _ ≤ Eratio * (((n : ℝ) ^ 2 * Ce * E) * 2) * ‖b‖ ^ 2 := by gcongr
      _ = _ := by ring

end RegularPointCoordinates

end

end OAI
