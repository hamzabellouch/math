import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitCoordinates

namespace OAI

/-! Actual classical first derivatives of the localized modes are L2.
The planar/transverse product formula and the volume-preserving chart give
membership without a smooth-compact-support assumption on the orbitals. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem normalizedPlanarMode_partial (e r : PlanarPosition) :
    planarPartial normalizedPlanarMode e r =
      (Real.sqrt (∫ s, planarResolventMode s ^ 2))⁻¹ * planarPartial planarResolventMode e r := by
  rw [normalizedPlanarMode_eq_const_mul, planarPartial_const_mul
    (planarResolventMode_C7.of_le (by norm_num))]

theorem normalizedPlanarMode_partial_square_integrable (e : PlanarPosition) :
    Integrable (fun r => planarPartial normalizedPlanarMode e r ^ 2) := by
  simp_rw [normalizedPlanarMode_partial, mul_pow]
  exact (planarResolventMode_partial_square_integrable e).const_mul _

theorem normalizedPlanarMode_partial_memLp (e : PlanarPosition) :
    MemLp (planarPartial normalizedPlanarMode e) 2 :=
  (memLp_two_iff_integrable_sq (planarPartial_continuous
    (normalizedPlanarMode_C7.of_le (by norm_num)) e).aestronglyMeasurable).mpr
    (normalizedPlanarMode_partial_square_integrable e)

theorem localizedMode_fderiv (freq : ℝ) (u : PlanarPosition) (p e : SplitPosition) :
    fderiv ℝ (localizedMode freq u) p e =
      planarPartial normalizedPlanarMode e.1 (p.1 - u) * verticalMode freq p.2 +
        normalizedPlanarMode (p.1 - u) * deriv (verticalMode freq) p.2 * e.2 := by
  have hp := (normalizedPlanarMode_C7.differentiable (by norm_num) (p.1 - u)).hasFDerivAt.comp p
    (hasFDerivAt_fst.sub_const u)
  have hv := (verticalMode_hasDerivAt freq p.2).hasFDerivAt.comp p hasFDerivAt_snd
  have h := congrArg (fun L : SplitPosition →L[ℝ] ℝ => L e) (hp.mul hv).fderiv
  have hfun : (fun q : SplitPosition => normalizedPlanarMode (q.1 - u) * verticalMode freq q.2) =
      localizedMode freq u := rfl
  have hh : fderiv ℝ (fun q : SplitPosition => normalizedPlanarMode (q.1 - u) * verticalMode freq q.2) p e =
      normalizedPlanarMode (p.1 - u) * (e.2 * (-freq * p.2 * verticalMode freq p.2)) +
        verticalMode freq p.2 * fderiv ℝ normalizedPlanarMode (p.1 - u) e.1 := by
    simpa only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.toSpanSingleton_apply, Function.comp_def, Pi.mul_def] using h
  rw [hfun] at hh
  rw [verticalMode_deriv]
  unfold planarPartial
  nlinarith only [hh]

theorem localizedMode_planarDerivative_memLp {freq : ℝ} (hfreq : 0 < freq)
    (u e : PlanarPosition) :
    MemLp (fun p : SplitPosition => planarPartial normalizedPlanarMode e (p.1 - u) * verticalMode freq p.2) 2 := by
  apply (memLp_two_iff_integrable_sq (by
    exact (((planarPartial_continuous (normalizedPlanarMode_C7.of_le (by norm_num)) e).comp
      (continuous_fst.sub continuous_const)).mul
      ((verticalMode_smooth freq).continuous.comp continuous_snd)).aestronglyMeasurable)).mpr
  simp_rw [mul_pow]
  rw [Measure.volume_eq_prod]
  exact ((normalizedPlanarMode_partial_square_integrable e).comp_sub_right u).mul_prod
    (verticalMode_square_integrable hfreq)

theorem localizedMode_verticalDerivative_memLp {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    MemLp (fun p : SplitPosition => normalizedPlanarMode (p.1 - u) * deriv (verticalMode freq) p.2) 2 := by
  apply (memLp_two_iff_integrable_sq (by
    exact ((normalizedPlanarMode_C7.continuous.comp (continuous_fst.sub continuous_const)).mul
      (((verticalMode_smooth freq).continuous_deriv (by simp)).comp continuous_snd)).aestronglyMeasurable)).mpr
  simp_rw [mul_pow]
  rw [Measure.volume_eq_prod]
  exact (normalizedPlanarMode_square_integrable.comp_sub_right u).mul_prod
    (verticalMode_deriv_square_integrable hfreq)

theorem localizedMode_fderiv_memLp {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) (e : SplitPosition) :
    MemLp (fun p => fderiv ℝ (localizedMode freq u) p e) 2 := by
  simp_rw [localizedMode_fderiv]
  exact (localizedMode_planarDerivative_memLp hfreq u e.1).add
    ((localizedMode_verticalDerivative_memLp hfreq u).mul_const e.2)

theorem continuumLocalizedMode_fderiv (freq : ℝ) (u : PlanarPosition) (x e : Position) :
    fderiv ℝ (continuumLocalizedMode freq u) x e =
      fderiv ℝ (localizedMode freq u) (positionSplitCoordinates x) (positionSplitCoordinates e) := by
  have h := ((localizedMode_C7 freq u).differentiable (by norm_num) (positionSplitCoordinates x)).hasFDerivAt.comp x
    positionSplitCoordinates.hasFDerivAt
  exact congrArg (fun L : Position →L[ℝ] ℝ => L e) h.fderiv

theorem continuumLocalizedMode_fderiv_memLp {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) (e : Position) :
    MemLp (fun x => fderiv ℝ (continuumLocalizedMode freq u) x e) 2 := by
  simp_rw [continuumLocalizedMode_fderiv]
  exact (localizedMode_fderiv_memLp hfreq u (positionSplitCoordinates e)).comp_measurePreserving
    positionSplitCoordinates_measurePreserving

end ContinuumCoulomb

end

end OAI
