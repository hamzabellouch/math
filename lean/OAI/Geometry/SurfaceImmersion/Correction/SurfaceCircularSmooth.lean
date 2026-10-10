import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceCircularThreshold
import OAI.Geometry.SurfaceImmersion.Primitive.CircularFrozenCoefficients

namespace OAI

/-! Smoothness of the actual circular surface profile on the selected
jet neighborhood. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation

lemma surfaceCircularProfile_smoothOn {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {U : Set Base} {Ω Z : TopologicalSpace.Opens GeometricJet}
    (hΩ : (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a)
    (hZΩ : (Z : Set GeometricJet) ⊆ Ω)
    {e₁ e₂ : GeometricJet → Vec} (h₁ : ContDiffOn ℝ ∞ e₁ Ω) (h₂ : ContDiffOn ℝ ∞ e₂ Ω)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ)) :
    ContDiffOn ℝ ∞ (surfaceCircularProfile F a e₁ e₂ α)
      ((CollarVelocity.jetSection F ⁻¹' Z) ×ˢ univ) := by
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
  exact circularFamilyProfile_smoothOn hV (hx.sub hv) hx hy hc hR
    (h₁.comp hσ.contDiffOn hmaps) (h₂.comp hσ.contDiffOn hmaps) hα' hD dy

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
