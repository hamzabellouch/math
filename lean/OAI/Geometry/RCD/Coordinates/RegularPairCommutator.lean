import OAI.Geometry.RCD.Coordinates.RegularRebasedRadialData
import OAI.Geometry.RCD.Coordinates.RestrictedCommutatorFit

namespace OAI

/-! # The actual commutator on the common radial-fit ball -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [BorelSpace X] [ProperSpace X] in
/-- The centered finite column and the centered linear family are exactly
the same Sobolev map, before any local representatives are chosen. -/
theorem centered_transformed_columnMap (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (N : Euclidean n ≃L[ℝ] Euclidean n)
    (eta : SobolevSpace μ hQ) (z : Euclidean n) :
    sobolevColumnMap μ hQ (centeredColumn μ hQ (transformedColumn μ hQ u N)
      ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) eta) =
      (centeredSobolevMap μ hQ u eta z).comp N.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro b
  have hh := centered_frame_covector_eq μ hQ u N eta z
    ((N : Euclidean n →L[ℝ] Euclidean n).adjoint z) (N b) (by
      rw [N.symm_apply_apply, ContinuousLinearMap.adjoint_inner_left]
      rfl)
  simpa only [N.symm_apply_apply, ContinuousLinearMap.comp_apply, centeredSobolevMap_apply,
    ContinuousLinearEquiv.coe_coe] using hh

/-- The published commutator bound applies to any chosen radial families
on the common small ball. The sole loss is its explicit volume ratio. -/
theorem regular_pair_commutator {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (haction : LocalPoissonHessianActionInput hX)
    {base first center : X} {a κ B J C A Cχ enlargement zeta eta Cg D Ca : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hcenter : center ∈ ball base (e.heat.radius / 32))
    (d1 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca first)
    (d2 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca center)
    (hκ : 0 ≤ κ) (hK : -κ ≤ K) (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hA : 0 ≤ A) (hCχ : 0 ≤ Cχ) (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1) (i : ℕ) :
    let μ := hausdorff n X
    let s := distanceSourceRadius e.heat.radius i
    let U := (centeredSobolevMap μ hX.quadratic e.heat.coordinates e.one.sobolev
      (e.heat.values center)).comp (d2.frame i).toContinuousLinearMap
    let Ω := ball center (s / 2048)
    dist center first ≤ s / 4 →
    ∀ G H : Euclidean n →L[ℝ] SobolevSpace μ hX.quadratic,
    (∀ b, SobolevSpace.toLp μ hX.quadratic (G b) =ᵐ[μ.restrict Ω]
      localGamma μ hX.quadratic (d2.replacement.replacement i) (U b)) →
    (∀ b, SobolevSpace.toLp μ hX.quadratic (H b) =ᵐ[μ.restrict Ω]
      localGamma μ hX.quadratic (d2.replacement.replacement i - d1.replacement.replacement i) (U b)) →
    ∀ b, (μ.real Ω)⁻¹ * (∫ x in Ω,
      (localGamma μ hX.quadratic (d2.replacement.replacement i - d1.replacement.replacement i) (G b) x -
        localGamma μ hX.quadratic (d2.replacement.replacement i) (H b) x -
        localGamma μ hX.quadratic (d2.replacement.replacement i - d1.replacement.replacement i) (U b) x) ^ 2 ∂μ) ≤
      ((5 / 3 : ℝ) * ((1 / 32 : ℝ) ^ n)⁻¹) * poissonCommutatorConstant n A 1 B J Cχ *
        s ^ 2 * ‖b‖ ^ 2 * (normalizedPoissonDefect μ hX.quadratic d1.source i +
          normalizedPoissonDefect μ hX.quadratic d2.source i) := by
  intro μ s U Ω hroom G H hG hH b
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hsR : s ≤ e.heat.radius := by
    have hh := distanceSourceRadius_outer_le e.heat.radius_pos.le i
    change 2 * s ≤ e.heat.radius at hh
    linarith
  let u := centeredColumn μ hX.quadratic
    (transformedColumn μ hX.quadratic e.heat.coordinates (d2.frame i))
    ((d2.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint (e.heat.values center)) e.one.sobolev
  have hU : sobolevColumnMap μ hX.quadratic u = U := centered_transformed_columnMap μ hX.quadratic _ _ _ _
  have hone := e.oneRepresentative center hcenter i
  have hfirst := ((d2.splitting i).mono_error μ hX.quadratic hzeta hzeta1).center μ hX.quadratic
    ((d2.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint (e.heat.values center)) e.one.sobolev hone
  have hsub4 : ball center (s / 4) ⊆ ball center (2 * s) := ball_subset_ball (by linarith)
  have hf1 := d1.gradient i center hroom
  have hf2 := d2.gradient i center (by simp only [dist_self]; positivity)
  have hvolume := e.volume center hcenter (s / 64) (by positivity) (by linarith)
  obtain ⟨g, h, hg, hh, he⟩ := normalized_poisson_commutator_error hX haction hκ hK hB hJ hCχ
    hA (by norm_num : (0 : ℝ) ≤ 1) first center center d1.source d2.source
    d1.replacement d2.replacement i hroom (by simp only [dist_self]; positivity) u
    (fun j => (hfirst.harmonic j).mono μ hX.quadratic hsub4)
    (fun j => ae_restrict_of_ae_restrict_of_subset hsub4 (hfirst.gradient j)) hf1 hf2
    (d2.cutoff i) hvolume b
  rw [hU] at hg hh he
  have hsub : Ω ⊆ ball center (s / 64) := ball_subset_ball (by linarith)
  have hbig : 0 < μ.real (ball center (s / 64)) :=
    (quarter_volume_bounds (by positivity) (euclideanUnitVolume_pos n) hvolume).1
  have hsmallVolume := e.volume center hcenter (s / 2048) (by positivity) (by linarith)
  have hsmall : 0 < μ.real Ω := (quarter_volume_bounds (by positivity) (euclideanUnitVolume_pos n) hsmallVolume).1
  have hratio : μ.real (ball center (s / 64)) ≤
      ((5 / 3 : ℝ) * ((1 / 32 : ℝ) ^ n)⁻¹) * μ.real Ω := by
    apply (div_le_iff₀ hsmall).mp
    exact radial_fraction_volume_ratio (by positivity : 0 < s / 64)
      (by norm_num : (0 : ℝ) < 1 / 32) (euclideanUnitVolume_pos n) hvolume
      (by simpa only [show (1 / 32 : ℝ) * (s / 64) = s / 2048 by ring] using hsmallVolume)
  have hsub64 : ball center (s / 64) ⊆ ball center (s / 4) := ball_subset_ball (by linarith)
  have hf := ae_restrict_of_ae_restrict_of_subset hsub64 hf2
  have hv : ∀ᵐ x ∂μ.restrict (ball center (s / 64)),
      localGamma μ hX.quadratic (d2.replacement.replacement i - d1.replacement.replacement i)
        (d2.replacement.replacement i - d1.replacement.replacement i) x ≤ (2 * A * s) ^ 2 := by
    have hneg : localGamma μ hX.quadratic (-d1.replacement.replacement i) (-d1.replacement.replacement i) =ᵐ[μ]
        localGamma μ hX.quadratic (d1.replacement.replacement i) (d1.replacement.replacement i) := by
      filter_upwards [localGamma_smul_left μ hX.quadratic (-1) (d1.replacement.replacement i) (-d1.replacement.replacement i),
        localGamma_smul_right μ hX.quadratic (-1) (d1.replacement.replacement i) (d1.replacement.replacement i)] with x h1 h2
      simp only [neg_one_smul, neg_one_mul] at h1 h2
      exact h1.trans ((congrArg Neg.neg h2).trans (neg_neg _))
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub64 hf1, hf,
      ae_restrict_of_ae hneg, ae_restrict_of_ae
        (localGamma_add_self_le μ hX.quadratic (d2.replacement.replacement i) (-d1.replacement.replacement i))]
      with x h1 h2 hneg hsum
    rw [← sub_eq_add_neg, hneg] at hsum
    nlinarith only [h1, h2, hsum]
  have hE : 0 ≤ poissonCommutatorConstant n A 1 B J Cχ * s ^ 2 * ‖b‖ ^ 2 *
      (normalizedPoissonDefect μ hX.quadratic d1.source i + normalizedPoissonDefect μ hX.quadratic d2.source i) := by
    have h1 := normalizedPoissonDefect_nonneg μ hX.quadratic d1.source hκ i
    have h2 := normalizedPoissonDefect_nonneg μ hX.quadratic d2.source hκ i
    have := euclideanUnitVolume_pos n
    dsimp only [poissonCommutatorConstant]
    positivity
  have hb := normalized_commutator_restrict μ hX.quadratic hsub hbig hsmall
    (d2.replacement.replacement i) (d2.replacement.replacement i - d1.replacement.replacement i)
    (U b) g h (G b) (H b) hf hv hg hh (hG b) (hH b) hE hratio he
  convert hb using 1
  ring

end RegularPointCoordinates

end

end OAI
