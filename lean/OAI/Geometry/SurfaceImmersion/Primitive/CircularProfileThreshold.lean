import OAI.Geometry.SurfaceImmersion.Geometry.FrozenCoefficientBounds

namespace OAI

/-! Fixed coefficient bounds and a spatial turn threshold, chosen before
any angular function or any of its derivatives. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_circular_profile_threshold {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hQ : ContDiffOn ℝ ∞ Q U) (hX : ContDiffOn ℝ ∞ X U)
    (hY : ContDiffOn ℝ ∞ Y U) (hC : ContDiffOn ℝ ∞ C U)
    (hR : ContDiffOn ℝ ∞ R U) (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hframe : ∀ x ∈ U, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hRpos : ∀ x ∈ U, 0 < R x) (d : E) :
    ∃ sLo sHi D : ℝ, 0 < sLo ∧ 0 < sHi ∧ 0 ≤ D ∧
      ∀ H : ℝ, 0 ≤ H → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ (α : E → ℝ) x, x ∈ K → DifferentiableAt ℝ α x → ∀ β : ℝ,
        circularSpatialProfile Q X Y C R e₁ e₂ α β x d ∈ regularBoundaryProfiles ∧
        sLo ≤ profileCoefficients (circularSpatialProfile Q X Y C R e₁ e₂ α β x d) 0 ∧
        profileCoefficients (circularSpatialProfile Q X Y C R e₁ e₂ α β x d) 0 ≤ sHi ∧
        |profileCoefficients (circularSpatialProfile Q X Y C R e₁ e₂ α β x d) 1| ≤ D ∧
        (Λ < fderiv ℝ α x d →
          H+2 < |profileCoefficients (circularSpatialProfile Q X Y C R e₁ e₂ α β x d) 2|) := by
  obtain ⟨sLo,sHi,D,hsLo,hsHi,hD0,hcoef⟩ := compact_frozen_coefficient_bounds
    hU hK hKU hQ hX hY hC hR h₁ h₂ hD hframe (fun x hx => (hRpos x hx).ne') d
  obtain ⟨B,hB,herror⟩ := compact_spatialError_bound_on hU hK hKU hQ hR h₁ h₂ d
  have hrcont : ContinuousOn R K := hR.continuousOn.mono hKU
  rcases K.eq_empty_or_nonempty with hE | hne
  · refine ⟨sLo,sHi,D,hsLo,hsHi,hD0,fun H _ => ⟨1,zero_lt_one,?_⟩⟩
    simp [hE]
  obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn hne hrcont
  have hr : 0 < R p := hRpos p (hKU hp)
  refine ⟨sLo,sHi,D,hsLo,hsHi,hD0,fun H hH =>
    ⟨(H+1+4*B+1)/(R p),div_pos (by positivity) hr,?_⟩⟩
  intro α x hx hα β
  have hxU := hKU hx
  have hf := hframe x hxU
  have hQx := (hQ.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have hRx := (hR.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have h1x := (h₁.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have h2x := (h₂.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have hreg : circularSpatialProfile Q X Y C R e₁ e₂ α β x d ∈ regularBoundaryProfiles :=
    circularBoundaryProfile_regular (hD x hxU) (hRpos x hxU).ne'
      hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.2
  refine ⟨hreg,?_,?_,?_,?_⟩
  · exact (hcoef x hx (α x)).1
  · exact (hcoef x hx (α x)).2.1
  · rw [circularSpatialProfile_first β hQx hRx h1x h2x hα hf]
    exact (hcoef x hx (α x)).2.2
  · intro hlarge
    have hh := circularSpatialProfile_mixed_dominates (X := X) (Y := Y) (C := C) β hQx hRx h1x h2x hα
      (hD x hxU) hf hr (hmin hx) hB (by linarith : 0 ≤ H+1) (herror α x hx) hlarge
    linarith

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
