import OAI.Geometry.SurfaceImmersion.Primitive.ActualFixedFrameLoop
import OAI.Geometry.SurfaceImmersion.Primitive.LocalCircularFamilyThreshold

namespace OAI

/-! Freeze the circular coefficient bounds on the original surface before
choosing its supported angle and its smaller jet neighborhood. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation

def surfaceCircularProfile (F : Base → Vec) (a : Base → ℝ)
    (e₁ e₂ : GeometricJet → Vec) (α : GeometricJet × ℝ → ℝ) : Base × ℝ → BoundaryProfile :=
  circularFamilyProfile
    (fun x => coordDeriv dx F x - jetNormal (CollarVelocity.jetSection F x))
    (coordDeriv dx F) (coordDeriv dy F) (coordDeriv dy (coordDeriv dy F))
    (fun x => velocityRadius (jetNormal (CollarVelocity.jetSection F x)) (a x))
    (e₁ ∘ CollarVelocity.jetSection F) (e₂ ∘ CollarVelocity.jetSection F)
    (fun z => α (CollarVelocity.jetSection F z.1,z.2)) dy

theorem compact_surface_circular_threshold {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {U K : Set Base} {Ω : TopologicalSpace.Opens GeometricJet}
    (hΩ : (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a)
    (hK : IsCompact K) (hKΩ : CollarVelocity.jetSection F '' K ⊆ Ω)
    {e₁ e₂ : GeometricJet → Vec} (h₁ : ContDiffOn ℝ ∞ e₁ Ω) (h₂ : ContDiffOn ℝ ∞ e₂ Ω)
    (hframe : ∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
      j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0) :
    ∃ sLo sHi D : ℝ, 0 < sLo ∧ 0 < sHi ∧ 0 ≤ D ∧
      ∀ H : ℝ, 0 ≤ H → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ Z : TopologicalSpace.Opens GeometricJet, CollarVelocity.jetSection F '' K ⊆ Z →
        (Z : Set GeometricJet) ⊆ Ω →
      ∀ α : GeometricJet × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) →
      ∀ x ∈ K, ∀ t : ℝ,
        let J := surfaceCircularProfile F a e₁ e₂ α (x,t)
        J ∈ regularBoundaryProfiles ∧
        sLo ≤ profileCoefficients J 0 ∧ profileCoefficients J 0 ≤ sHi ∧
        |profileCoefficients J 1| ≤ D ∧
        (Λ < fderiv ℝ (fun z => α (CollarVelocity.jetSection F z.1,z.2)) (x,t) (dy,0) →
          H+2 < |profileCoefficients J 2|) := by
  let V : Set Base := CollarVelocity.jetSection F ⁻¹' Ω
  have hσ := CollarVelocity.jetSection_smooth hF
  have hV : IsOpen V := Ω.isOpen.preimage hσ.continuous
  have hKV : K ⊆ V := fun x hx => hKΩ (mem_image_of_mem _ hx)
  have hmaps : MapsTo (CollarVelocity.jetSection F) V Ω := fun _ hx => hx
  have hD : ∀ x ∈ V, gramDet (coordDeriv dy F x) (coordDeriv dy (coordDeriv dy F) x) ≠ 0 :=
    fun x hx => preferredJetDomain_velocity_gram (hΩ hx).1
  have hv : ContDiffOn ℝ ∞ (fun x => jetNormal (CollarVelocity.jetSection F x)) V :=
    (jetNormal_smooth (fun j hj => preferredJetDomain_velocity_gram (hΩ hj).1)).comp hσ.contDiffOn hmaps
  have hnonzero : ∀ x ∈ V, jetNormal (CollarVelocity.jetSection F x) ≠ 0 ∨ a x ≠ 0 :=
    fun _ hx => (hΩ hx).2
  have hR := velocityRadius_smoothOn hv ha.contDiffOn hnonzero
  have hx := (contDiff_real_coordDeriv hF dx).contDiffOn (s := V)
  have hy := (contDiff_real_coordDeriv hF dy).contDiffOn (s := V)
  have hc := (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy).contDiffOn (s := V)
  obtain ⟨sLo,sHi,D,hsLo,hsHi,hD0,hbounds⟩ := compact_circular_family_threshold_local
    hV hK hKV (hx.sub hv) hx hy hc hR
    (h₁.comp hσ.contDiffOn hmaps) (h₂.comp hσ.contDiffOn hmaps) hD
    (fun x hx => hframe (CollarVelocity.jetSection F x) hx)
    (fun x hx => velocityRadius_pos (hnonzero x hx)) dy
  refine ⟨sLo,sHi,D,hsLo,hsHi,hD0,?_⟩
  intro H hH
  obtain ⟨Λ,hΛ,hbound⟩ := hbounds H hH
  refine ⟨Λ,hΛ,?_⟩
  intro Z hKZ hZΩ α hα x hx t
  let W : Set Base := CollarVelocity.jetSection F ⁻¹' Z
  have hW : IsOpen W := Z.isOpen.preimage hσ.continuous
  have hKW : K ⊆ W := fun x hx => hKZ (mem_image_of_mem _ hx)
  have hWV : W ⊆ V := fun _ hx => hZΩ hx
  have hα' : ContDiffOn ℝ ∞ (fun z : Base × ℝ => α (CollarVelocity.jetSection F z.1,z.2))
      (W ×ˢ univ) :=
    hα.comp ((hσ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn (fun _ hz => ⟨hz.1,hz.2⟩)
  exact hbound W hW hKW hWV _ hα' x hx t

lemma surfaceCircularProfile_turn_iff {F n : Base → Vec} {a : Base → ℝ}
    {U : Set Base} {Ω : Set GeometricJet} (hΩ : Ω ⊆ supportedJetDomain U n a)
    {e₁ e₂ : GeometricJet → Vec}
    (hframe : ∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
      j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0)
    (α : GeometricJet × ℝ → ℝ) {x : Base} (hx : CollarVelocity.jetSection F x ∈ Ω) (t : ℝ) :
    profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 3 = 0 ↔
      fderiv ℝ (fun z => α (CollarVelocity.jetSection F z.1,z.2)) (x,t) (0,1) = 0 := by
  exact circularFamilyProfile_turn_iff _ _ _ _ _ _ _ _ _ _ _
    (preferredJetDomain_velocity_gram (hΩ hx).1)
    (velocityRadius_pos (hΩ hx).2).ne' (hframe _ hx)

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
