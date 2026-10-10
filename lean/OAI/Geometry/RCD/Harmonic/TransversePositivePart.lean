import OAI.Geometry.RCD.Coordinates.TransverseCoordinateEnergy
import OAI.Geometry.RCD.Sobolev.SobolevLevelChain

namespace OAI

/-! # A positive transverse test with an explicit axial derivative -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem transverse_positive_test (w s η : SobolevSpace μ Q) (Ω : Set X)
    (W S : X → ℝ)
    (hW : SobolevSpace.toLp μ Q w =ᵐ[μ.restrict Ω] W)
    (hS : SobolevSpace.toLp μ Q s =ᵐ[μ.restrict Ω] S)
    (hη : SobolevSpace.toLp μ Q η =ᵐ[μ.restrict Ω] fun _ => (1:ℝ))
    (hww : localGamma μ Q w w =ᵐ[μ.restrict Ω] fun _ => (1:ℝ))
    (hsw : localGamma μ Q s w =ᵐ[μ.restrict Ω] fun _ => (0:ℝ))
    (δ c : ℝ) :
    let P := (w+δ • η).upperPositivePart μ Q (le_refl (0:ℝ))
    let T := (c • η-s).upperPositivePart μ Q (le_refl (0:ℝ))
    ∀ (A B : ℝ≥0)
      (_hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q P x|≤A)
      (_hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q T x|≤B),
      localGamma μ Q (SobolevSpace.product μ Q P T A B) w =ᵐ[μ.restrict Ω]
        fun x => if -δ<W x then max (c-S x) 0 else 0 := by
  intro P T A B hA hB
  let U := w+δ • η
  let V := c • η-s
  have he : localGamma μ Q η w =ᵐ[μ.restrict Ω] fun _ => (0:ℝ) := by
    filter_upwards [hη,ae_restrict_of_ae (localGamma_zero_on_level μ Q η w 1)] with x hx hz
    exact hz hx
  have hu : SobolevSpace.toLp μ Q U =ᵐ[μ.restrict Ω] fun x => W x+δ := by
    change SobolevSpace.toLpCLM μ Q (w+δ • η) =ᵐ[μ.restrict Ω] _
    rw [map_add,map_smul]
    filter_upwards [hW,hη,ae_restrict_of_ae (Lp.coeFn_add (SobolevSpace.toLp μ Q w)
      (δ • SobolevSpace.toLp μ Q η)),ae_restrict_of_ae (Lp.coeFn_smul δ (SobolevSpace.toLp μ Q η))]
      with x hw hηx ha hs
    change (SobolevSpace.toLp μ Q w+δ • SobolevSpace.toLp μ Q η) x=W x+δ
    simp only [ha,Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,hw,hηx,mul_one]
  have hv : SobolevSpace.toLp μ Q V =ᵐ[μ.restrict Ω] fun x => c-S x := by
    change SobolevSpace.toLpCLM μ Q (c • η-s) =ᵐ[μ.restrict Ω] _
    rw [map_sub,map_smul]
    filter_upwards [hS,hη,ae_restrict_of_ae (Lp.coeFn_sub (c • SobolevSpace.toLp μ Q η)
      (SobolevSpace.toLp μ Q s)),ae_restrict_of_ae (Lp.coeFn_smul c (SobolevSpace.toLp μ Q η))]
      with x hs hηx hsub hsm
    change (c • SobolevSpace.toLp μ Q η-SobolevSpace.toLp μ Q s) x=c-S x
    simp only [hsub,Pi.sub_apply,hsm,Pi.smul_apply,smul_eq_mul,hs,hηx,mul_one]
  have hUw : localGamma μ Q U w =ᵐ[μ.restrict Ω] fun _ => (1:ℝ) := by
    filter_upwards [hww,he,ae_restrict_of_ae (localGamma_add_left μ Q w (δ • η) w),
      ae_restrict_of_ae (localGamma_smul_left μ Q δ η w)] with x hw he hx hs
    change localGamma μ Q (w+δ • η) w x=1
    simp only [hx,hs,hw,he,mul_zero,add_zero]
  have hVw : localGamma μ Q V w =ᵐ[μ.restrict Ω] fun _ => (0:ℝ) := by
    filter_upwards [hsw,he,ae_restrict_of_ae (localGamma_sub_left μ Q (c • η) s w),
      ae_restrict_of_ae (localGamma_smul_left μ Q c η w)] with x hw he hx hs
    change localGamma μ Q (c • η-s) w x=0
    simp only [hx,hs,hw,he,mul_zero,sub_zero]
  filter_upwards [hu,hv,hUw,hVw,
    ae_restrict_of_ae (localGamma_upperPositivePart μ Q U w (le_refl (0:ℝ))),
    ae_restrict_of_ae (localGamma_upperPositivePart μ Q V w (le_refl (0:ℝ))),
    ae_restrict_of_ae (V.upperPositivePart_coe μ Q (le_refl (0:ℝ))),
    ae_restrict_of_ae (localGamma_product_left μ Q P T w A B hA hB)]
    with x hu hv hUw hVw hP hT hTv hp
  rw [hp]
  change localGamma μ Q (U.upperPositivePart μ Q (le_refl (0:ℝ))) w x=_ at hP
  change localGamma μ Q (V.upperPositivePart μ Q (le_refl (0:ℝ))) w x=_ at hT
  have hTc : SobolevSpace.toLp μ Q T x=max (c-S x) 0 := by
    simpa only [upperLevelPart,hv,sub_zero] using hTv
  rw [hP,hT,hUw,hVw,hTc,hu]
  simp only [ite_self,mul_zero,zero_add]
  by_cases hx : -δ<W x
  · rw [ite_eq_left hx,ite_eq_left (by linarith : 0<W x+δ),mul_one]
  · rw [ite_eq_right hx,ite_eq_right (by linarith : ¬0<W x+δ),mul_zero]

end RegularPointCoordinates

end

end OAI
