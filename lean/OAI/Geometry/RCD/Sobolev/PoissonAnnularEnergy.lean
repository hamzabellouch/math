import OAI.Geometry.RCD.Sobolev.PoissonCaccioppoli
import OAI.Geometry.RCD.Sobolev.PoissonCutoffSource

namespace OAI

/-! # Energy control of the annular Poisson error without a gradient bound -/

open Set Filter Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- A second cutoff covering the transition annulus controls its cross
source by the equation and the amplitude of the original solution. -/
theorem IsConstantLaplacianOn.annular_error_L1_le
    {Ω : Set X} (hfin : μ Ω ≠ ∞)
    (f η : SobolevSpace μ hQ) (c : ℝ) (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (A : ℝ≥0) (hApos : 0 < (A:ℝ))
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ A)
    {χ : X → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hsupp : tsupport χ ⊆ Ω) (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ] χ)
    {p : X} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (ξ : GoodLaplacianCutoff μ hQ p R C)
    (hinside : closedBall p (2*R) ⊆ Ω)
    (hone : ∀ x, R ≤ dist x p → dist x p ≤ 2*R → χ x = 1)
    (e : Lp ℝ 2 μ) (hei : Integrable e μ)
    (herep : e =ᵐ[μ] fun x => 2*localGamma μ hQ f ξ.sobolev x)
    (hes : ∀ᵐ x ∂μ, e x ≠ 0 → R ≤ dist x p ∧ dist x p ≤ 2*R) :
    (∫ x, |e x| ∂μ) ≤
      (2*|c|+4*(A:ℝ)*(L:ℝ)^2+(A:ℝ)*(C/R)^2)*μ.real Ω := by
  let G := SobolevSpace.minimalSlope μ hQ f
  have hgξ := SobolevSpace.minimalSlope_le_lipschitz μ hQ ξ.sobolev ξ.lipschitz ξ.representative
  have hcross : ∀ᵐ x ∂μ, |localGamma μ hQ f ξ.sobolev x| ≤ G x*(C/R) := by
    filter_upwards [localGamma_abs_le μ hQ f ξ.sobolev,hgξ,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ f)] with x hc hg hG
    rw [Real.coe_toNNReal _ (div_nonneg hC hR.le)] at hg
    exact hc.trans (mul_le_mul_of_nonneg_left hg hG)
  have hi : Integrable (fun x => (χ x)^2*(G x)^2) μ := by
    have hηb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ (1:ℝ≥0) := by
      filter_upwards [hη] with x hx
      rw [hx,abs_of_nonneg (hb x).1]
      exact (hb x).2
    apply (bounded_square_weight_integrable μ (SobolevSpace.toLp μ hQ η) G hηb).congr
    filter_upwards [hη] with x hx
    rw [hx]
  have hezero : ∀ᵐ x ∂μ, x ∉ Ω → |e x| = 0 := by
    filter_upwards [hes] with x hx hnot
    by_cases he : e x = 0
    · simp only [he,abs_zero]
    · exact (hnot (hinside (hx he).2)).elim
  have heq : (∫ x, |e x| ∂μ) = ∫ x in Ω, |e x| ∂μ :=
    (setIntegral_eq_integral_of_ae_compl_eq_zero hezero).symm
  have hpoint : ∀ᵐ x ∂μ.restrict Ω,
      |e x| ≤ (χ x)^2*(G x)^2/(A:ℝ)+(A:ℝ)*(C/R)^2 := by
    filter_upwards [ae_restrict_of_ae herep,ae_restrict_of_ae hes,
      ae_restrict_of_ae hcross] with x he hx hc
    by_cases he0 : e x = 0
    · rw [he0,abs_zero]
      positivity
    have hχone : χ x = 1 := hone x (hx he0).1 (hx he0).2
    rw [he,abs_mul,show |(2:ℝ)| = 2 by norm_num,hχone,one_pow,one_mul]
    apply (mul_le_mul_iff_right₀ hApos).mp
    have hid : (A:ℝ)*((G x)^2/(A:ℝ)+(A:ℝ)*(C/R)^2) =
        (G x)^2+(A:ℝ)^2*(C/R)^2 := by field_simp
    rw [hid]
    have hc' := mul_le_mul_of_nonneg_right hc hApos.le
    nlinarith only [hc',sq_nonneg (G x-(A:ℝ)*(C/R))]
  have henergy := hf.cutoff_energy_le μ hQ hfin f η c hχ hs hb hsupp hη hA
  have hpart : (∫ x in Ω, (χ x)^2*(G x)^2 ∂μ) ≤ ∫ x, (χ x)^2*(G x)^2 ∂μ :=
    setIntegral_le_integral hi (Filter.Eventually.of_forall fun x => by positivity)
  have hip : Integrable (fun x => (χ x)^2*(G x)^2/(A:ℝ)+(A:ℝ)*(C/R)^2) (μ.restrict Ω) := by
    simpa only [Pi.add_apply] using! (hi.div_const (A:ℝ)).integrableOn.add
      (integrableOn_const (C := (A:ℝ)*(C/R)^2) hfin)
  rw [heq]
  calc
    _ ≤ ∫ x in Ω, (χ x)^2*(G x)^2/(A:ℝ)+(A:ℝ)*(C/R)^2 ∂μ :=
      integral_mono_ae hei.abs.integrableOn hip hpoint
    _ = (∫ x in Ω, (χ x)^2*(G x)^2 ∂μ)/(A:ℝ)+(A:ℝ)*(C/R)^2*μ.real Ω := by
      rw [integral_add (hi.div_const _).integrableOn (integrableOn_const hfin),
        integral_div, setIntegral_const,smul_eq_mul,mul_comm (μ.real Ω)]
    _ ≤ (∫ x, (χ x)^2*(G x)^2 ∂μ)/(A:ℝ)+(A:ℝ)*(C/R)^2*μ.real Ω :=
      by linarith [div_le_div_of_nonneg_right hpart hApos.le]
    _ ≤ ((2*|c| *(A:ℝ)+4*(A:ℝ)^2*(L:ℝ)^2)*μ.real Ω)/(A:ℝ)+
        (A:ℝ)*(C/R)^2*μ.real Ω :=
      by linarith [div_le_div_of_nonneg_right henergy hApos.le]
    _ = _ := by field_simp

/-- The same estimate written directly for the cutoff cross density. -/
theorem IsConstantLaplacianOn.cutoff_cross_L1_le
    {Ω : Set X} (hfin : μ Ω ≠ ∞)
    (f η : SobolevSpace μ hQ) (c : ℝ) (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (A : ℝ≥0) (hApos : 0 < (A:ℝ))
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ A)
    {χ : X → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hsupp : tsupport χ ⊆ Ω) (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ] χ)
    {p : X} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (ξ : GoodLaplacianCutoff μ hQ p R C)
    (hinside : closedBall p (2*R) ⊆ Ω)
    (hone : ∀ x, R ≤ dist x p → dist x p ≤ 2*R → χ x = 1) :
    (∫ x, |2*localGamma μ hQ f ξ.sobolev x| ∂μ) ≤
      (2*|c|+4*(A:ℝ)*(L:ℝ)^2+(A:ℝ)*(C/R)^2)*μ.real Ω := by
  obtain ⟨b,e,_,_,hei,herep,hes⟩ :=
    hf.cutoff_source_decomposition μ hQ f c A hA hR hC ξ hinside
  have hbound := hf.annular_error_L1_le μ hQ hfin f η c A hApos hA
    hχ hs hb hsupp hη hR hC ξ hinside hone e hei herep hes
  have heq : (∫ x, |e x| ∂μ) = ∫ x, |2*localGamma μ hQ f ξ.sobolev x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [herep] with x hx
    rw [hx]
  rwa [heq] at hbound

end RegularPointCoordinates

end

end OAI
