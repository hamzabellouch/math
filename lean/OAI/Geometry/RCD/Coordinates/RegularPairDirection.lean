import OAI.Geometry.RCD.Coordinates.RegularPairCoordinates
import OAI.Geometry.RCD.Harmonic.TwoCenterDirectionEstimate

namespace OAI

/-! # Constant-direction recovery for the actual two-center replacements -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

/-- The dimensionless value coefficient after restriction and frame transport. -/
def regularRadialValueCoefficient (n : ℕ) (B D : ℝ) : ℝ :=
  2 * ((5 / 3 : ℝ) * ((1 / 32 : ℝ) ^ n)⁻¹) * (n : ℝ) ^ 2 *
    (2 * D ^ 2 + 8192 * ((n : ℝ) * 2) ^ 2 * B *
      ((4 / (3 * euclideanUnitVolume n)) * (64 : ℝ) ^ n)) / 64 ^ 2

/-- The dimensionless energy coefficient for the same transported residual. -/
def regularRadialEnergyCoefficient (K : ℝ) (n : ℕ) (Cg A B J Cχ D : ℝ) : ℝ :=
  2 * ((5 / 3 : ℝ) * ((1 / 16 : ℝ) ^ n)⁻¹) * (n : ℝ) ^ 2 *
    (radialEnergyConstant K n Cg 1 A B J Cχ *
      ((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹ * D ^ 2 +
        (4 / (3 * euclideanUnitVolume n)) * (128 : ℝ) ^ n))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The pairing is constructed from the actual radial derivatives. Every
smallness premise here is an explicit scalar bound on the already constructed
source envelopes; no direction or mass estimate is assumed. -/
theorem regular_pair_direction {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (haction : LocalPoissonHessianActionInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (hmean : LocalHarmonicL2MeanValueInput hX) (hn : 2 ≤ n)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ Cgrad Cmean : ℝ, 1 ≤ Cgrad ∧ 1 ≤ Cmean ∧
    ∀ {base first center : X} {a B J C A Cχ enlargement zeta eta Cg D Ca : ℝ}
      {ker : ℝ → X → X → ℝ}
      {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
      (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
      (_hfirst : first ∈ ball base (e.heat.radius / 32))
      (_hcenter : center ∈ ball base (e.heat.radius / 32))
      (d1 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca first)
      (d2 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca center),
    -κ ≤ K → 0 ≤ B → 0 ≤ J → 0 ≤ A → 0 ≤ Cχ → 0 ≤ zeta → zeta ≤ 1 →
    (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * (2 : ℝ) ^ n) * zeta) ≤ 1 / 3 →
    (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * (8192 : ℝ) ^ n) * zeta) ≤ 1 / 2 →
    ∀ i,
    let μ := hausdorff n X
    let s := distanceSourceRadius e.heat.radius i
    let U := (centeredSobolevMap μ hX.quadratic e.heat.coordinates e.one.sobolev
      (e.heat.values center)).comp (d2.frame i).toContinuousLinearMap
    let delta := (d2.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint
      (e.heat.values first - e.heat.values center)
    let Ω := ball center (s / 2048)
    let E1 := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant n Cχ * zeta)
      (normalizedPoissonDefect μ hX.quadratic d1.source) i
    let E2 := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant n Cχ * zeta)
      (normalizedPoissonDefect μ hX.quadratic d2.source) i
    let Vc := regularRadialValueCoefficient n B D
    let Ec := regularRadialEnergyCoefficient K n Cg A B J Cχ D
    let Com := ((5 / 3 : ℝ) * ((1 / 32 : ℝ) ^ n)⁻¹) * poissonCommutatorConstant n A 1 B J Cχ *
      s ^ 2 * (normalizedPoissonDefect μ hX.quadratic d1.source i +
        normalizedPoissonDefect μ hX.quadratic d2.source i)
    let amax := 4 * (Cgrad / (s / 2048))
    let err := (2 * A * s) * Real.sqrt (Ec * E2) + Real.sqrt Com +
      (A * s) * Real.sqrt (2 * (Ec * E2) + 2 * (Ec * E1)) +
      Real.sqrt (2 * (Vc * s ^ 2 * E2) + 2 * (Vc * s ^ 2 * E1)) / 4
    dist first center ≤ s / 512 → -κ ≤ K * (s / 2048) ^ 2 →
    2 * ((n : ℝ) ^ 4 * Real.sqrt (2 * Ca ^ 2 *
      (D ^ 2 * E1 + radialFitQualitativeConstant n Cχ * zeta))) ≤ 1 / 2 →
    2 * ((n : ℝ) ^ 4 * Real.sqrt (2 * Ca ^ 2 *
      (D ^ 2 * E2 + radialFitQualitativeConstant n Cχ * zeta))) ≤ 1 / 4 →
    amax * Real.sqrt (Vc * s ^ 2 * E2) ≤ 1 / 2 →
    ∃ H : Euclidean n →L[ℝ] SobolevSpace μ hX.quadratic,
      (∀ b, SobolevSpace.toLp μ hX.quadratic (H b) =ᵐ[μ.restrict Ω]
        localGamma μ hX.quadratic (d2.replacement.replacement i - d1.replacement.replacement i) (U b)) ∧
      ∀ b, ‖normalizeLocalL2 μ Ω (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hX.quadratic Ω
          (H b - ⟪delta, b⟫_ℝ • e.one.sobolev))‖ ≤
        (Real.sqrt (2 * (Vc * s ^ 2 * E2) + 2 * (Vc * s ^ 2 * E1)) +
          s * (2 * amax * err) + 2 * (2 * Cmean * err + (2 * s) * (2 * amax * err))) * ‖b‖ := by
  obtain ⟨Cgrad, Cmean, hCgrad, hCmean, hrecover⟩ := two_center_direction_estimate hgradient hmean hn hκ
  refine ⟨Cgrad, Cmean, hCgrad, hCmean, ?_⟩
  intro base first center a B J C A Cχ enlargement zeta eta Cg D Ca ker hk
    e hfirst hcenter d1 d2 hK hB hJ hA hCχ hzeta hzeta1 hframe hgram i
    μ s U delta Ω E1 E2 Vc Ec Com amax err hroom hcurv hMx hMz habsorb
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hE1 : 0 ≤ E1 := (radial_fit_pinching_envelope_budget d1.source hκ hCχ hzeta d1.summable).2.2 i |>.1
  have hE2 : 0 ≤ E2 := (radial_fit_pinching_envelope_budget d2.source hκ hCχ hzeta d2.summable).2.2 i |>.1
  have hVc : 0 ≤ Vc := by dsimp only [Vc, regularRadialValueCoefficient]; have := euclideanUnitVolume_pos n; positivity
  have hEc : 0 ≤ Ec := by
    have := (radialEnergyConstant_pos (K := K) (n := n) (G := Cg) (ε := 1) (A := A) hB hJ hCχ).le
    dsimp only [Ec, regularRadialEnergyCoefficient]
    have := euclideanUnitVolume_pos n
    positivity
  have hCom : 0 ≤ Com := by
    have := normalizedPoissonDefect_nonneg μ hX.quadratic d1.source hκ i
    have := normalizedPoissonDefect_nonneg μ hX.quadratic d2.source hκ i
    have := euclideanUnitVolume_pos n
    dsimp only [Com, poissonCommutatorConstant]
    positivity
  have hamax : 0 ≤ amax := by dsimp only [amax]; positivity
  have herr : 0 ≤ err := by dsimp only [err]; positivity
  obtain ⟨Ax, Gx, hAx, hx⟩ := regular_rebased_radial_data hX e hfirst hcenter d1 d2
    hκ hB hJ hCχ hzeta hframe i hroom
  obtain ⟨Az, Gz, hAz, hz⟩ := regular_rebased_radial_data hX e hcenter hcenter d2 d2
    hκ hB hJ hCχ hzeta hframe i (by simp only [dist_self]; positivity)
  have hAx' : ‖Ax - 1‖ ≤ 1 / 2 := hAx.trans hMx
  have hAz' : ‖Az - 1‖ ≤ 1 / 4 := hAz.trans hMz
  have hGx (b) := (hx b).1
  have hGz (b) := (hz b).1
  let d : Euclidean n →L[ℝ] ℝ := innerSL ℝ delta
  let c := d.comp Ax
  have hzv (b) : ‖normalizeLocalL2 μ Ω (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hX.quadratic Ω (Gz b - U (Az b)))‖ ^ 2 ≤
      (Vc * s ^ 2 * E2) * ‖b‖ ^ 2 := by
    have hh := (hz b).2.1
    simp only [sub_self, map_zero, inner_zero_left, zero_smul, add_zero] at hh
    convert hh using 1
    dsimp only [Vc, regularRadialValueCoefficient]
    ring
  have hze (b) : (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hX.quadratic
      (Gz b - U (Az b)) (Gz b - U (Az b)) x ∂μ) ≤ (Ec * E2) * ‖b‖ ^ 2 := by
    have hh := (hz b).2.2
    simp only [sub_self, map_zero, inner_zero_left, zero_smul, add_zero] at hh
    convert hh using 1
    dsimp only [Ec, regularRadialEnergyCoefficient]
    ring
  have hxv (b) : ‖normalizeLocalL2 μ Ω (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hX.quadratic Ω (Gx b - U (Ax b) + c b • e.one.sobolev))‖ ^ 2 ≤
      (Vc * s ^ 2 * E1) * ‖b‖ ^ 2 := by
    have hh := (hx b).2.1
    convert hh using 1 <;> first | rfl | (dsimp only [c, d, U, delta, μ, Ω, s,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, Vc, regularRadialValueCoefficient]; ring)
  have hxe (b) : (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hX.quadratic
      (Gx b - U (Ax b) + c b • e.one.sobolev)
      (Gx b - U (Ax b) + c b • e.one.sobolev) x ∂μ) ≤ (Ec * E1) * ‖b‖ ^ 2 := by
    have hh := (hx b).2.2
    convert hh using 1 <;> first | rfl | (dsimp only [c, d, U, delta, μ, Ω, s,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, Ec, regularRadialEnergyCoefficient]; ring)
  let u := centeredColumn μ hX.quadratic
    (transformedColumn μ hX.quadratic e.heat.coordinates (d2.frame i))
    ((d2.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint (e.heat.values center)) e.one.sobolev
  let V := fun x => (d2.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint
    (e.heat.values x - e.heat.values center)
  have hU : sobolevColumnMap μ hX.quadratic u = U := centered_transformed_columnMap μ hX.quadratic _ _ _ _
  obtain ⟨hfirstOrder, hzero, N, hN, hNnorm, hvalues⟩ := regular_pair_coordinates hX e hcenter d2 hzeta hzeta1 hgram i
  change ∀ b, ‖normalizeLocalL2 μ Ω _ (SobolevSpace.restrictLp μ hX.quadratic Ω
    (sobolevColumnMap μ hX.quadratic u b))‖ ≤ s * ‖b‖ at hvalues
  rw [hU] at hvalues
  have hsub : Ω ⊆ ball center (2 * s) := ball_subset_ball (by linarith)
  have hone := ae_restrict_of_ae_restrict_of_subset hsub (e.oneRepresentative center hcenter i)
  have hdelta : ‖delta‖ ≤ s := by
    have hh := (d2.metric i).centered_norm_error (by positivity : 0 < s / 64) (by norm_num)
      (by simp only [sub_self, smul_zero]) (by linarith : dist first center ≤ 4 * (s / 64))
    simp only [← map_sub] at hh
    change _ ∧ ‖(s / 64)⁻¹ • delta‖ ≤ 4 + zeta at hh
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (s / 64)⁻¹)] at hh
    have hv := mul_le_mul_of_nonneg_left hh.2 (by positivity : 0 ≤ s / 64)
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity : s / 64 ≠ 0), one_mul] at hv
    change ‖delta‖ ≤ s / 64 * (4 + zeta) at hv
    nlinarith only [hv, mul_le_mul_of_nonneg_left hzeta1 hs.le, hs.le]
  have hc : ‖c‖ ≤ 2 * s := by
    have hdnorm : ‖d‖ ≤ s := by simpa only [d, innerSL_apply_norm] using hdelta
    have hAnorm : ‖Ax‖ ≤ 2 := by
      calc
        _ = ‖(Ax - 1) + 1‖ := by rw [sub_add_cancel]
        _ ≤ ‖Ax - 1‖ + ‖(1 : Euclidean n →L[ℝ] Euclidean n)‖ := norm_add_le _ _
        _ ≤ 2 := by
          have hid : ‖(1 : Euclidean n →L[ℝ] Euclidean n)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
          linarith only [hAx', hid]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hdnorm hAnorm (norm_nonneg _) hs.le).trans_eq (by ring))
  have hf := ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (by linarith : s / 2048 ≤ s / 4))
    (d2.gradient i center (by simp only [dist_self]; positivity))
  have hfx := ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (by linarith : s / 2048 ≤ s / 4))
    (d1.gradient i center (by rw [dist_comm]; linarith))
  have hv : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hX.quadratic
      (d2.replacement.replacement i - d1.replacement.replacement i)
      (d2.replacement.replacement i - d1.replacement.replacement i) x ≤ (2 * A * s) ^ 2 := by
    have hneg : localGamma μ hX.quadratic (-d1.replacement.replacement i) (-d1.replacement.replacement i) =ᵐ[μ]
        localGamma μ hX.quadratic (d1.replacement.replacement i) (d1.replacement.replacement i) := by
      filter_upwards [localGamma_smul_left μ hX.quadratic (-1) (d1.replacement.replacement i) (-d1.replacement.replacement i),
        localGamma_smul_right μ hX.quadratic (-1) (d1.replacement.replacement i) (d1.replacement.replacement i)] with x h1 h2
      simp only [neg_one_smul, neg_one_mul] at h1 h2
      exact h1.trans ((congrArg Neg.neg h2).trans (neg_neg _))
    filter_upwards [hf, hfx, ae_restrict_of_ae hneg, ae_restrict_of_ae
      (localGamma_add_self_le μ hX.quadratic (d2.replacement.replacement i) (-d1.replacement.replacement i))]
      with x h1 h2 h3 h4
    rw [← sub_eq_add_neg, h3] at h4
    nlinarith only [h1, h2, h4]
  have hH (b) := radial_difference_representative μ hX.quadratic Ω
    (d2.replacement.replacement i) (d1.replacement.replacement i) (U b) (Gz b) (Gx b) (hGz b) (hGx b)
  have hcomm (b) := regular_pair_commutator hX haction e hcenter d1 d2 hκ hK hB hJ hA hCχ hzeta hzeta1 i
    (by rw [dist_comm]; linarith) Gz (Gz - Gx) hGz hH b
  have hanorm : 2 * ‖N.toContinuousLinearMap‖ * (Cgrad / (s / 2048)) ≤ amax := by
    dsimp only [amax]
    nlinarith only [mul_le_mul_of_nonneg_right hNnorm (by positivity : 0 ≤ Cgrad / (s / 2048))]
  have hasmall : 2 * ‖N.toContinuousLinearMap‖ * (Cgrad / (s / 2048)) *
      Real.sqrt (Vc * s ^ 2 * E2) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hanorm (Real.sqrt_nonneg _)).trans habsorb
  have hr := hrecover center (s / 2048) (by positivity) hcurv u V N hN
    (fun j => (hfirstOrder.harmonic j).mono μ hX.quadratic hsub)
    (hfirstOrder.continuous.mono hsub) hzero
    (fun j => ae_restrict_of_ae_restrict_of_subset hsub (hfirstOrder.representative j))
    e.one.sobolev (d2.replacement.replacement i) (d1.replacement.replacement i)
    Gz Gx Az Ax c d (A * s) (2 * A * s) (Vc * s ^ 2 * E2) (Vc * s ^ 2 * E1)
    (Ec * E2) (Ec * E1) s (2 * s) Com
  dsimp only at hr
  rw [hU] at hr
  have hcomm' (b) : (μ.real Ω)⁻¹ * (∫ x in Ω,
      (localGamma μ hX.quadratic (d2.replacement.replacement i - d1.replacement.replacement i) (Gz b) x -
        localGamma μ hX.quadratic (d2.replacement.replacement i) ((Gz - Gx) b) x -
        localGamma μ hX.quadratic (d2.replacement.replacement i - d1.replacement.replacement i) (U b) x) ^ 2 ∂μ) ≤
      Com * ‖b‖ ^ 2 := by
    convert hcomm b using 1
    dsimp only [Com]
    ring
  obtain ⟨_, _, hdir⟩ := hr (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) hs.le hCom hAz' hAx' hasmall rfl hc hone hvalues hf hv
    hGz hGx hzv hxv hze hxe hcomm'
  have he : (2 * A * s) * Real.sqrt (Ec * E2) + Real.sqrt Com +
      (A * s) * Real.sqrt (2 * (Ec * E2) + 2 * (Ec * E1)) +
      Real.sqrt (2 * (Vc * s ^ 2 * E2) + 2 * (Vc * s ^ 2 * E1)) * ‖Az - 1‖ ≤ err := by
    dsimp only [err]
    nlinarith only [mul_le_mul_of_nonneg_left hAz'
      (Real.sqrt_nonneg (2 * (Vc * s ^ 2 * E2) + 2 * (Vc * s ^ 2 * E1)))]
  refine ⟨Gz - Gx, hH, ?_⟩
  intro b
  apply (hdir b).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg b)
  have hamul := mul_le_mul hanorm he (by positivity) hamax
  have hcmul := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ Cmean)
  dsimp only
  nlinarith only [mul_le_mul_of_nonneg_left hamul hs.le, hcmul]

end RegularPointCoordinates

end

end OAI
