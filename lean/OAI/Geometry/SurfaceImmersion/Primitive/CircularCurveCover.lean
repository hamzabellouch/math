import OAI.Geometry.SurfaceImmersion.Primitive.CircularFamilyThreshold
import OAI.Geometry.SurfaceImmersion.Primitive.ActualProfileCurveCover

namespace OAI

/-! The constructed circular profiles preserve every later curve using the
old positive collar invariant and the fixed interior turn threshold. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes SmallModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_circular_curve_cover {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
    {U K C₀ I : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hC₀ : IsClosed C₀) (hI : IsClosed I) (hcover : ∀ x ∈ K, x ∈ C₀ ∨ x ∈ I)
    (hQ : ContDiffOn ℝ ∞ Q U) (hX : ContDiffOn ℝ ∞ X U)
    (hY : ContDiffOn ℝ ∞ Y U) (hC : ContDiffOn ℝ ∞ C U)
    (hR : ContDiffOn ℝ ∞ R U) (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hframe : ∀ x ∈ U, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hRpos : ∀ x ∈ U, 0 < R x) (d : E) (B : ℝ) (hB : 0 ≤ B) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ α : E × ℝ → ℝ,
      ContDiffOn ℝ ∞ α (U ×ˢ univ) →
      (∀ x ∈ K ∩ I, ∀ t ∈ Icc (0 : ℝ) 1, fderiv ℝ α (x,t) (0,1) = 0 →
        Λ < fderiv ℝ α (x,t) (d,0)) →
      ∀ b c k : E → ℝ, ContinuousOn b U → ContinuousOn c U → ContinuousOn k U →
      (∀ x ∈ K, b x ≠ 0 ∨ c x ≠ 0) → (∀ x ∈ K, -B ≤ k x) →
      (∀ x ∈ K ∩ C₀, ∀ t ∈ Icc (0 : ℝ) 1,
        0 < (profileCoefficients (circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t)) 1*b x +
          profileCoefficients (circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t)) 0*c x)^2 + k x*b x^2) →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η →
      ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ F : RField 4, ContDiff ℝ ∞ F →
      ∀ p : Base, ‖realBoundaryProfile F z p-circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t)‖ < η →
      k x ≤ coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p →
      realSecondForm F (b x,c x) (b x,c x) p ≠ 0 ∧
      normalize (realSecondForm F (b x,c x) (b x,c x) p) ≠
        -profilePreferred (realBoundaryProfile F z p) := by
  let Z : Set (E × ℝ) := K ×ˢ Icc (0 : ℝ) 1
  let : CompactSpace Z := isCompact_iff_compactSpace.mp (hK.prod isCompact_Icc)
  let C' : Set Z := {w | w.val.1 ∈ C₀}
  let I' : Set Z := {w | w.val.1 ∈ I}
  have hc' : IsClosed C' := hC₀.preimage (continuous_fst.comp continuous_subtype_val)
  have hi' : IsClosed I' := hI.preimage (continuous_fst.comp continuous_subtype_val)
  have hcover' : ∀ w : Z, w ∈ C' ∨ w ∈ I' := fun w => hcover w.val.1 w.property.1
  obtain ⟨sLo,sHi,D,hsLo,_,hD0,hbounds⟩ := compact_circular_family_threshold
    hU hK hKU hQ hX hY hC hR h₁ h₂ hD hframe hRpos d
  obtain ⟨H,hH,hcurve⟩ := compact_actual_profile_curve_cover hc' hi' hcover' sLo B D hsLo hB hD0
  obtain ⟨Λ,hΛ,hprofile⟩ := hbounds H hH.le
  refine ⟨Λ,hΛ,?_⟩
  intro α hα hturn b c k hb hc hk hbc hkb hcollar
  let J : Z → BoundaryProfile := fun w => circularFamilyProfile Q X Y C R e₁ e₂ α d w.val
  have hJ : Continuous J := by
    change Continuous (Z.domRestrict (circularFamilyProfile Q X Y C R e₁ e₂ α d))
    exact ContinuousOn.domRestrict
      ((circularFamilyProfile_smoothOn hU hQ hX hY hC hR h₁ h₂ hα hD d).continuousOn.mono
        (fun w hw => ⟨hKU hw.1,mem_univ _⟩))
  have hdata (w : Z) := hprofile α hα w.val.1 w.property.1 w.val.2
  have hturn' : ∀ w ∈ I', profileCoefficients (J w) 3 = 0 → H+2 < |profileCoefficients (J w) 2| := by
    intro w hw hz
    apply (hdata w).2.2.2.2
    apply hturn w.val.1 ⟨w.property.1,hw⟩ w.val.2 w.property.2
    exact (circularFamilyProfile_turn_iff Q X Y C e₁ e₂ R α d w.val.1 w.val.2
      (hD _ (hKU w.property.1)) (hRpos _ (hKU w.property.1)).ne'
      (hframe _ (hKU w.property.1))).mp hz
  have hposmap : ∀ f : E → ℝ, ContinuousOn f U → Continuous (fun w : Z => f w.val.1) := by
    intro f hf
    exact hf.comp_continuous (continuous_fst.comp continuous_subtype_val) (fun w => hKU w.property.1)
  obtain ⟨η,hη,hactual⟩ := hcurve J hJ (fun w => (hdata w).1)
    (fun w => (hdata w).2.1) (fun w => (hdata w).2.2.2.1) hturn'
    (fun w => b w.val.1) (fun w => c w.val.1) (fun w => k w.val.1)
    (hposmap b hb) (hposmap c hc) (hposmap k hk)
    (fun w => hbc w.val.1 w.property.1) (fun w => hkb w.val.1 w.property.1)
    (fun w hw => hcollar w.val.1 ⟨w.property.1,hw⟩ w.val.2 w.property.2)
  refine ⟨η,hη,?_⟩
  intro z hz hzη x hx t ht F hF p herr hcurv
  exact hactual z hz hzη ⟨(x,t),hx,ht⟩ F hF p herr hcurv

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
