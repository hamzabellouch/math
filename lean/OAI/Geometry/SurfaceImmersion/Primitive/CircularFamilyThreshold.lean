import OAI.Geometry.SurfaceImmersion.Primitive.CircularFamilyProfile

namespace OAI

/-! Bounds for the actual joint position/phase profile. All constants are
fixed before the angular function and its transverse derivatives. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_circular_family_threshold {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
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
      ∀ α : E × ℝ → ℝ, ContDiffOn ℝ ∞ α (U ×ˢ univ) →
      ∀ x ∈ K, ∀ t : ℝ,
      let J := circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t)
      J ∈ regularBoundaryProfiles ∧
      sLo ≤ profileCoefficients J 0 ∧ profileCoefficients J 0 ≤ sHi ∧
      |profileCoefficients J 1| ≤ D ∧
      (Λ < fderiv ℝ α (x,t) (d,0) → H+2 < |profileCoefficients J 2|) := by
  obtain ⟨sLo,sHi,D,hsLo,hsHi,hD0,hbounds⟩ := compact_circular_profile_threshold
    hU hK hKU hQ hX hY hC hR h₁ h₂ hD hframe hRpos d
  refine ⟨sLo,sHi,D,hsLo,hsHi,hD0,?_⟩
  intro H hH
  obtain ⟨Λ,hΛ,hprofile⟩ := hbounds H hH
  refine ⟨Λ,hΛ,?_⟩
  intro α hα x hx t
  have hxU := hKU hx
  have hαat : DifferentiableAt ℝ α (x,t) :=
    (hα.contDiffAt ((hU.prod isOpen_univ).mem_nhds
      (show (x,t) ∈ U ×ˢ univ from ⟨hxU,mem_univ t⟩))).differentiableAt (by simp)
  have hαslice : DifferentiableAt ℝ (fun y => α (y,t)) x :=
    hαat.comp x (differentiableAt_id.prodMk (differentiableAt_const t))
  have heq := circularFamilyProfile_spatial (X := X) (Y := Y) (C := C)
    ((hQ.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp))
    ((hR.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp))
    ((h₁.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp))
    ((h₂.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)) hαat d
  dsimp only
  rw [heq]
  obtain ⟨hreg,hlo,hhi,hd,hlarge⟩ := hprofile (fun y => α (y,t)) x hx hαslice
    (fderiv ℝ α (x,t) (0,1))
  refine ⟨hreg,hlo,hhi,hd,?_⟩
  intro hderiv
  apply hlarge
  rw [fderiv_slice_first hαat]
  exact hderiv

lemma circularFamilyProfile_turn_iff (Q X Y C e₁ e₂ : E → Vec) (R : E → ℝ)
    (α : E × ℝ → ℝ) (d x : E) (t : ℝ)
    (hD : gramDet (Y x) (C x) ≠ 0) (hR : R x ≠ 0)
    (hf : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0) :
    profileCoefficients (circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t)) 3 = 0 ↔
      fderiv ℝ α (x,t) (0,1) = 0 := by
  exact circularBoundaryProfile_turn_iff hD hR hf.1 hf.2.1 hf.2.2.1
    hf.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.2

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
