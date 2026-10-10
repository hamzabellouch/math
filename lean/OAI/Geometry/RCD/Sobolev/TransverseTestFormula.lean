import OAI.Geometry.RCD.Harmonic.TransversePositivePart

namespace OAI

/-! # The exact transverse test formula before imposing orthonormality -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem transverse_positive_test_formula (w s η : SobolevSpace μ Q) (Ω : Set X)
    (W S : X → ℝ)
    (hW : SobolevSpace.toLp μ Q w =ᵐ[μ.restrict Ω] W)
    (hS : SobolevSpace.toLp μ Q s =ᵐ[μ.restrict Ω] S)
    (hη : SobolevSpace.toLp μ Q η =ᵐ[μ.restrict Ω] fun _ => (1:ℝ))
    (δ c : ℝ) :
    let P := (w+δ • η).upperPositivePart μ Q (le_refl (0:ℝ))
    let T := (c • η-s).upperPositivePart μ Q (le_refl (0:ℝ))
    ∀ (A B : ℝ≥0)
      (_hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q P x|≤A)
      (_hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q T x|≤B),
      localGamma μ Q (SobolevSpace.product μ Q P T A B) w =ᵐ[μ.restrict Ω]
        fun x => (if -δ<W x then max (c-S x) 0*localGamma μ Q w w x else 0) -
          (if S x<c then max (W x+δ) 0*localGamma μ Q s w x else 0) := by
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
  have hUw : localGamma μ Q U w =ᵐ[μ.restrict Ω] localGamma μ Q w w := by
    filter_upwards [he,ae_restrict_of_ae (localGamma_add_left μ Q w (δ • η) w),
      ae_restrict_of_ae (localGamma_smul_left μ Q δ η w)] with x he hx hs
    change localGamma μ Q (w+δ • η) w x=_
    simp only [hx,hs,he,mul_zero,add_zero]
  have hVw : localGamma μ Q V w =ᵐ[μ.restrict Ω] fun x => -localGamma μ Q s w x := by
    filter_upwards [he,ae_restrict_of_ae (localGamma_sub_left μ Q (c • η) s w),
      ae_restrict_of_ae (localGamma_smul_left μ Q c η w)] with x he hx hs
    change localGamma μ Q (c • η-s) w x=_
    simp only [hx,hs,he,mul_zero,zero_sub]
  filter_upwards [hu,hv,hUw,hVw,
    ae_restrict_of_ae (localGamma_upperPositivePart μ Q U w (le_refl (0:ℝ))),
    ae_restrict_of_ae (localGamma_upperPositivePart μ Q V w (le_refl (0:ℝ))),
    ae_restrict_of_ae (V.upperPositivePart_coe μ Q (le_refl (0:ℝ))),
    ae_restrict_of_ae (U.upperPositivePart_coe μ Q (le_refl (0:ℝ))),
    ae_restrict_of_ae (localGamma_product_left μ Q P T w A B hA hB)]
    with x hu hv hUw hVw hP hT hTv hPv hp
  rw [hp]
  change localGamma μ Q (U.upperPositivePart μ Q (le_refl (0:ℝ))) w x=_ at hP
  change localGamma μ Q (V.upperPositivePart μ Q (le_refl (0:ℝ))) w x=_ at hT
  have hTc : SobolevSpace.toLp μ Q T x=max (c-S x) 0 := by
    simpa only [upperLevelPart,hv,sub_zero] using hTv
  have hPc : SobolevSpace.toLp μ Q P x=max (W x+δ) 0 := by
    simpa only [upperLevelPart,hu,sub_zero] using hPv
  rw [hP,hT,hUw,hVw,hTc,hPc,hu,hv]
  by_cases hx : -δ<W x
  · have hx' : 0<W x+δ := by linarith
    by_cases hy : S x<c
    · have hy' : 0<c-S x := by linarith
      simp only [hx,hx',hy,hy',ite_true]
      ring
    · have hy' : ¬0<c-S x := by linarith
      simp only [hx,hx',hy,hy',ite_true,ite_false,mul_zero,zero_add,sub_zero]
  · have hx' : ¬0<W x+δ := by linarith
    by_cases hy : S x<c
    · have hy' : 0<c-S x := by linarith
      simp only [hx,hx',hy,hy',ite_true,ite_false,mul_zero,zero_sub]
      ring
    · have hy' : ¬0<c-S x := by linarith
      simp only [hx,hx',hy,hy',ite_false,mul_zero,add_zero,sub_zero]

end RegularPointCoordinates

end

end OAI
