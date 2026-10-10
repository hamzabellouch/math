import OAI.Geometry.RCD.Harmonic.TransversePositivePart

namespace OAI

/-! # The compact barrier uses an actual product of bounded Sobolev functions -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
theorem bounded_positive_affine_bound (f g : SobolevSpace μ Q) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q f x|≤A)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q g x|≤B) (a : ℝ) :
    ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q
      ((f+a • g).upperPositivePart μ Q (le_refl (0:ℝ))) x|≤A+‖a‖₊*B := by
  have hc : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (f+a • g) x|≤A+‖a‖₊*B := by
    simp only [map_add,map_smul]
    filter_upwards [hf,hg,Lp.coeFn_add (SobolevSpace.toLp μ Q f) (a • SobolevSpace.toLp μ Q g),
      Lp.coeFn_smul a (SobolevSpace.toLp μ Q g)] with x hx hy ha hs
    rw [ha]
    simp only [Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,
      coe_nnnorm,Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (add_le_add hx (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)))
  filter_upwards [hc,(f+a • g).upperPositivePart_coe μ Q (le_refl (0:ℝ))] with x hx hy
  rw [hy]
  simp only [upperLevelPart,sub_zero]
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le ((le_abs_self _).trans hx) (by positivity)

theorem exists_bounded_transverse_test (w s η : SobolevSpace μ Q) (Ω : Set X)
    (W S : X → ℝ) (A B E : ℝ≥0)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q w x|≤A)
    (hs : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q s x|≤B)
    (he : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q η x|≤E)
    (hW : SobolevSpace.toLp μ Q w =ᵐ[μ.restrict Ω] W)
    (hS : SobolevSpace.toLp μ Q s =ᵐ[μ.restrict Ω] S)
    (hη : SobolevSpace.toLp μ Q η =ᵐ[μ.restrict Ω] fun _ => (1:ℝ))
    (hww : localGamma μ Q w w =ᵐ[μ.restrict Ω] fun _ => (1:ℝ))
    (hsw : localGamma μ Q s w =ᵐ[μ.restrict Ω] fun _ => (0:ℝ)) (δ c : ℝ) :
    ∃ f : SobolevSpace μ Q,
      (SobolevSpace.toLp μ Q f =ᵐ[μ.restrict Ω]
        fun x => max (W x+δ) 0*max (c-S x) 0) ∧
      (localGamma μ Q f w =ᵐ[μ.restrict Ω]
        fun x => if -δ<W x then max (c-S x) 0 else 0) := by
  let P := (w+δ • η).upperPositivePart μ Q (le_refl (0:ℝ))
  let T := (c • η-s).upperPositivePart μ Q (le_refl (0:ℝ))
  let C := A+‖δ‖₊*E
  let D := B+‖c‖₊*E
  have hP : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q P x|≤C := bounded_positive_affine_bound μ Q w η A E hw he δ
  have hneg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (-s) x|≤B := by
    simp only [map_neg]
    filter_upwards [hs,Lp.coeFn_neg (SobolevSpace.toLp μ Q s)] with x hx hy
    simpa only [hy,Pi.neg_apply,abs_neg] using hx
  have hT : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q T x|≤D := by
    simpa only [T,D,sub_eq_neg_add,NNReal.coe_add,NNReal.coe_mul] using
      bounded_positive_affine_bound μ Q (-s) η B E hneg he c
  refine ⟨SobolevSpace.product μ Q P T C D,?_,
    transverse_positive_test μ Q w s η Ω W S hW hS hη hww hsw δ c C D hP hT⟩
  have hU : SobolevSpace.toLp μ Q (w+δ • η) =ᵐ[μ.restrict Ω] fun x => W x+δ := by
    simp only [map_add,map_smul]
    filter_upwards [hW,hη,ae_restrict_of_ae (Lp.coeFn_add (SobolevSpace.toLp μ Q w)
      (δ • SobolevSpace.toLp μ Q η)),ae_restrict_of_ae (Lp.coeFn_smul δ (SobolevSpace.toLp μ Q η))]
      with x hx hy ha hm
    simp only [ha,Pi.add_apply,hm,Pi.smul_apply,smul_eq_mul,hx,hy,mul_one]
  have hV : SobolevSpace.toLp μ Q (c • η-s) =ᵐ[μ.restrict Ω] fun x => c-S x := by
    simp only [map_sub,map_smul]
    filter_upwards [hS,hη,ae_restrict_of_ae (Lp.coeFn_sub (c • SobolevSpace.toLp μ Q η)
      (SobolevSpace.toLp μ Q s)),ae_restrict_of_ae (Lp.coeFn_smul c (SobolevSpace.toLp μ Q η))]
      with x hx hy ha hm
    simp only [ha,Pi.sub_apply,hm,Pi.smul_apply,smul_eq_mul,hx,hy,mul_one]
  filter_upwards [ae_restrict_of_ae (SobolevSpace.product_coe μ Q P T C D hP hT),hU,hV,
    ae_restrict_of_ae ((w+δ • η).upperPositivePart_coe μ Q (le_refl (0:ℝ))),
    ae_restrict_of_ae ((c • η-s).upperPositivePart_coe μ Q (le_refl (0:ℝ)))]
    with x hx hu hv hp ht
  rw [hx]
  change SobolevSpace.toLp μ Q ((w+δ • η).upperPositivePart μ Q (le_refl (0:ℝ))) x *
    SobolevSpace.toLp μ Q ((c • η-s).upperPositivePart μ Q (le_refl (0:ℝ))) x = _
  rw [hp,ht]
  simp only [upperLevelPart,hu,hv,sub_zero]

end RegularPointCoordinates

end

end OAI
