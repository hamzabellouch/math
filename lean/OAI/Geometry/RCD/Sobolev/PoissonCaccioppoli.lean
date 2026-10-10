import OAI.Geometry.RCD.Sobolev.PoissonLocality
import OAI.Geometry.RCD.Harmonic.UnboundedCaccioppoli

namespace OAI

/-! # Local energy control for a bounded constant-source solution -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The source term adds its natural amplitude contribution to the usual
cutoff energy bound. No gradient bound on the Poisson solution is assumed. -/
theorem IsConstantLaplacianOn.cutoff_energy_le
    {Ω : Set X} (hfin : μ Ω ≠ ∞)
    (f η : SobolevSpace μ hQ) (c : ℝ) (hf : IsConstantLaplacianOn μ hQ Ω f c)
    {χ : X → ℝ} {L A : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hsupp : tsupport χ ⊆ Ω) (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ] χ)
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ A) :
    (∫ x, (χ x)^2*(SobolevSpace.minimalSlope μ hQ f x)^2 ∂μ) ≤
      (2*|c| *A+4*(A:ℝ)^2*(L:ℝ)^2)*μ.real Ω := by
  let F := SobolevSpace.toLp μ hQ f
  let H := SobolevSpace.minimalSlope μ hQ η
  have hχabs (x : X) : |χ x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (hb x).1]; exact (hb x).2
  let M := SobolevSpace.cutoffCLM μ hQ hχ hs hχabs (fun x => (hb x).1)
  have hH : ∀ᵐ x ∂μ, |H x| ≤ L := by
    filter_upwards [SobolevSpace.minimalSlope_le_lipschitz μ hQ η hχ hη,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ η)] with x hx h0
    rw [abs_of_nonneg h0]
    exact hx
  have hval : SobolevSpace.toLp μ hQ (M (M f)) =ᵐ[μ] fun x => (χ x)^2*F x := by
    filter_upwards [SobolevSpace.cutoffCLM_coe μ hQ hχ hs hχabs (fun x => (hb x).1) (M f),
      SobolevSpace.cutoffCLM_coe μ hQ hχ hs hχabs (fun x => (hb x).1) f] with x h1 h2
    change SobolevSpace.toLp μ hQ (M (M f)) x = _ at h1
    change SobolevSpace.toLp μ hQ (M f) x = _ at h2
    rw [h1,h2]
    ring
  have htestB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (M (M f)) x| ≤ A := by
    filter_upwards [hval,hA] with x hx ha
    rw [hx,abs_mul,abs_pow,abs_of_nonneg (hb x).1]
    have hc : (χ x)^2 ≤ 1 := by nlinarith [(hb x).1,(hb x).2]
    exact (mul_le_mul_of_nonneg_right hc (abs_nonneg (F x))).trans (by simpa using ha)
  have he : energyForm μ hQ f (M (M f)) ≤ |c| *A*μ.real Ω := by
    rw [hf _ (SobolevSpace.cutoffCLM_mem_dirichlet μ hQ hχ hs hχabs
      (fun x => (hb x).1) hsupp (M f))]
    have hI := norm_setIntegral_le_of_norm_le_const_ae
      (f := fun x => SobolevSpace.toLp μ hQ (M (M f)) x) (C := (A:ℝ)) hfin.lt_top
      (by simpa only [Real.norm_eq_abs] using (ae_restrict_of_ae (s := Ω) htestB))
    have hm := mul_le_mul_of_nonneg_left hI (abs_nonneg c)
    calc
      _ ≤ |(-c)*(∫ x in Ω, SobolevSpace.toLp μ hQ (M (M f)) x ∂μ)| := le_abs_self _
      _ = |c| *‖∫ x in Ω, SobolevSpace.toLp μ hQ (M (M f)) x ∂μ‖ := by
        rw [abs_mul,abs_neg,Real.norm_eq_abs]
      _ ≤ _ := by convert hm using 1; ring
  have hIz : ∀ᵐ x ∂μ, x ∉ Ω → F x^2*H x^2 = 0 := by
    filter_upwards [hη,SobolevSpace.minimalSlope_zero_on_level μ hQ η 0] with x he hz hx
    have hc : χ x = 0 := by
      by_contra hne
      exact hx (hsupp (subset_tsupport χ hne))
    have hH0 : H x = 0 := hz (he.trans hc)
    rw [hH0,zero_pow (by decide),mul_zero]
  have hIi : Integrable (fun x => F x^2*H x^2) μ := by
    simpa only [mul_comm] using! bounded_square_weight_integrable μ H F hH
  have hIb : (∫ x, F x^2*H x^2 ∂μ) ≤ (A:ℝ)^2*(L:ℝ)^2*μ.real Ω := by
    rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hIz]
    calc
      _ ≤ ∫ _x in Ω, (A:ℝ)^2*(L:ℝ)^2 ∂μ := by
        apply integral_mono_ae hIi.integrableOn (integrableOn_const hfin)
        filter_upwards [ae_restrict_of_ae hA,ae_restrict_of_ae hH] with x ha hh
        have hfa : F x^2 ≤ (A:ℝ)^2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (F x)) ha 2
        have hha : H x^2 ≤ (L:ℝ)^2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (H x)) hh 2
        exact mul_le_mul hfa hha (sq_nonneg _) (sq_nonneg _)
      _ = _ := by rw [setIntegral_const,smul_eq_mul]; ring
  have henergy := caccioppoli_cutoffCLM_energy μ hQ f η hχ hs hχabs
    (fun x => (hb x).1) hη hH
  have hleft : (∫ x, (SobolevSpace.toLp μ hQ η x)^2*
      (SobolevSpace.minimalSlope μ hQ f x)^2 ∂μ) =
      ∫ x, (χ x)^2*(SobolevSpace.minimalSlope μ hQ f x)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hη] with x hx
    rw [hx]
  rw [hleft] at henergy
  change _ ≤ 2*energyForm μ hQ f (M (M f))+4*(∫ x, F x^2*H x^2 ∂μ) at henergy
  nlinarith only [henergy,he,hIb]

end RegularPointCoordinates

end

end OAI
