import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceBoundaryCollar

namespace OAI

/-! Identify the first two coefficients of the actual surface profiles with
those used to choose the boundary collar before the loop. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation

lemma surfaceCircularProfile_frozen_coefficients {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {U : Set Base} {Ω Z : TopologicalSpace.Opens GeometricJet}
    (hΩ : (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a)
    (hZΩ : (Z : Set GeometricJet) ⊆ Ω)
    {e₁ e₂ : GeometricJet → Vec} (h₁ : ContDiffOn ℝ ∞ e₁ Ω) (h₂ : ContDiffOn ℝ ∞ e₂ Ω)
    (hframe : ∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
      j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    {x : Base} (hxZ : CollarVelocity.jetSection F x ∈ Z) (t : ℝ) :
    profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 0 =
      surfaceFrozenSize F a e₁ e₂ (x,α (CollarVelocity.jetSection F x,t)) ∧
    profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 1 =
      surfaceFrozenFirst F a e₁ e₂ (x,α (CollarVelocity.jetSection F x,t)) := by
  let V : Set Base := CollarVelocity.jetSection F ⁻¹' Z
  have hσ := CollarVelocity.jetSection_smooth hF
  have hV : IsOpen V := Z.isOpen.preimage hσ.continuous
  have hmaps : MapsTo (CollarVelocity.jetSection F) V Ω := fun _ hx => hZΩ hx
  have hD : ∀ x ∈ V, gramDet (coordDeriv dy F x) (coordDeriv dy (coordDeriv dy F) x) ≠ 0 :=
    fun x hx => preferredJetDomain_velocity_gram (hΩ (hZΩ hx)).1
  have hv : ContDiffOn ℝ ∞ (fun x => jetNormal (CollarVelocity.jetSection F x)) V :=
    (jetNormal_smooth (fun j hj => preferredJetDomain_velocity_gram (hΩ hj).1)).comp hσ.contDiffOn hmaps
  have hnonzero : ∀ x ∈ V, jetNormal (CollarVelocity.jetSection F x) ≠ 0 ∨ a x ≠ 0 :=
    fun _ hx => (hΩ (hZΩ hx)).2
  have hR := velocityRadius_smoothOn hv ha.contDiffOn hnonzero
  have hx := (contDiff_real_coordDeriv hF dx).contDiffOn (s := V)
  have hy := (contDiff_real_coordDeriv hF dy).contDiffOn (s := V)
  have hc := (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy).contDiffOn (s := V)
  have hα' : ContDiffOn ℝ ∞ (fun z : Base × ℝ => α (CollarVelocity.jetSection F z.1,z.2))
      (V ×ˢ univ) :=
    hα.comp ((hσ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn (fun _ hz => ⟨hz.1,hz.2⟩)
  have hnb := hV.mem_nhds hxZ
  exact circularFamilyProfile_frozen_coefficients
    (X := coordDeriv dx F) (Y := coordDeriv dy F) (C := coordDeriv dy (coordDeriv dy F))
    (((hx.sub hv).contDiffAt hnb).differentiableAt (by simp))
    ((hR.contDiffAt hnb).differentiableAt (by simp))
    (((h₁.comp hσ.contDiffOn hmaps).contDiffAt hnb).differentiableAt (by simp))
    (((h₂.comp hσ.contDiffOn hmaps).contDiffAt hnb).differentiableAt (by simp))
    ((hα'.contDiffAt ((hV.prod isOpen_univ).mem_nhds (show (x,t) ∈ V ×ˢ univ from ⟨hxZ,mem_univ t⟩))).differentiableAt (by simp))
    (hframe _ (hZΩ hxZ)) dy

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
