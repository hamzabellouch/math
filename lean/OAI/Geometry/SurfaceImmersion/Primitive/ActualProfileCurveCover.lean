import OAI.Geometry.SurfaceImmersion.Whitney.ActualProfileCollar

namespace OAI

/-! Combine the zero-amplitude collar with the interior turn estimate on a
compact curve. The turn threshold is fixed before the loop is selected. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem compact_actual_profile_curve_cover {C D : Set X}
    (hC : IsClosed C) (hD : IsClosed D) (hcover : ∀ x, x ∈ C ∨ x ∈ D)
    (sLo K d : ℝ) (hsLo : 0 < sLo) (hK : 0 ≤ K) (hd : 0 ≤ d) :
    ∃ H : ℝ, 0 < H ∧ ∀ J : X → BoundaryProfile, Continuous J →
      (∀ x, J x ∈ regularBoundaryProfiles) →
      (∀ x, sLo ≤ profileCoefficients (J x) 0) →
      (∀ x, |profileCoefficients (J x) 1| ≤ d) →
      (∀ x ∈ D, profileCoefficients (J x) 3 = 0 → H+2 < |profileCoefficients (J x) 2|) →
      ∀ b c k : X → ℝ, Continuous b → Continuous c → Continuous k →
      (∀ x, b x ≠ 0 ∨ c x ≠ 0) → (∀ x, -K ≤ k x) →
      (∀ x ∈ C, 0 < (profileCoefficients (J x) 1 * b x +
        profileCoefficients (J x) 0 * c x)^2 + k x*b x^2) →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η → ∀ x : X,
      ∀ F : RField 4, ContDiff ℝ ∞ F → ∀ p : Base,
      ‖realBoundaryProfile F z p-J x‖ < η →
      k x ≤ coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p →
      realSecondForm F (b x,c x) (b x,c x) p ≠ 0 ∧
      normalize (realSecondForm F (b x,c x) (b x,c x) p) ≠
        -profilePreferred (realBoundaryProfile F z p) := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  obtain ⟨H,hH,hcurve⟩ := compact_actual_profile_curves (X := D) sLo K d hsLo hK hd
  refine ⟨H,hH,?_⟩
  intro J hJ hreg hS hDb hturn b c k hb hc hk hbc hkb hcollar
  obtain ⟨ηd,hηd,hinterior⟩ := hcurve (fun x => J x.val) (hJ.comp continuous_subtype_val)
    (fun x => hreg x.val) (fun x => hS x.val) (fun x => hDb x.val)
    (fun x => hturn x.val x.property)
  obtain ⟨ηc,hηc,hcollar'⟩ := compact_actual_profile_collar (X := C)
    (hJ.comp continuous_subtype_val) (fun x => hreg x.val)
    (hb.comp continuous_subtype_val) (hc.comp continuous_subtype_val) (hk.comp continuous_subtype_val)
    (fun x => hcollar x.val x.property)
  refine ⟨min ηc ηd,lt_min hηc hηd,?_⟩
  intro z hz hzη x F hF p herr hcurv
  rcases hcover x with hx | hx
  · exact hcollar' ⟨x,hx⟩ F hF z p (herr.trans_le (min_le_left _ _)) hcurv
  · exact hinterior z hz (hzη.trans_le (min_le_right _ _)) ⟨x,hx⟩ F hF p
      (herr.trans_le (min_le_right _ _)) ((hkb x).trans hcurv) (b x) (c x) (hbc x)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
