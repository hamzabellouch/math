import OAI.Geometry.SurfaceImmersion.Correction.SurfaceCircularSmooth
import OAI.Geometry.SurfaceImmersion.Whitney.ZeroAmplitudeCollar

namespace OAI

/-! Apply the zero-amplitude collar estimate to the actual immersion and
its preferred jet frame. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation CollarVelocity

def surfaceFrozenFirst (F : Base → Vec) (a : Base → ℝ) (e₁ e₂ : GeometricJet → Vec) : Base × ℝ → ℝ :=
  frozenFirst (fun x => coordDeriv dx F x-jetNormal (jetSection F x))
    (coordDeriv dx F) (coordDeriv dy F) (coordDeriv dy (coordDeriv dy F))
    (fun x => velocityRadius (jetNormal (jetSection F x)) (a x))
    (e₁ ∘ jetSection F) (e₂ ∘ jetSection F) dy

def surfaceFrozenSize (F : Base → Vec) (a : Base → ℝ) (e₁ e₂ : GeometricJet → Vec) : Base × ℝ → ℝ :=
  frozenSize (coordDeriv dx F) (coordDeriv dy F) (coordDeriv dy (coordDeriv dy F))
    (fun x => velocityRadius (jetNormal (jetSection F x)) (a x))
    (e₁ ∘ jetSection F) (e₂ ∘ jetSection F)

theorem surface_zero_amplitude_collar {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {U K C₀ : Set Base} {Ω : TopologicalSpace.Opens GeometricJet}
    (hΩ : (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a)
    (hK : IsCompact K) (hKΩ : jetSection F '' K ⊆ Ω) (hC₀ : IsClosed C₀)
    (hzero : ∀ x ∈ C₀, a x = 0)
    {e₁ e₂ : GeometricJet → Vec} (h₁ : ContDiffOn ℝ ∞ e₁ Ω) (h₂ : ContDiffOn ℝ ∞ e₂ Ω)
    (hframe : ∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
      j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0)
    {B : Set GeometricJet} (hB : IsOpen B) (hCB : jetSection F '' C₀ ⊆ B)
    (hBadapt : ∀ j ∈ B, e₁ j = normalize (jetNormal j))
    {b c k : Base → ℝ}
    (hb : ContDiffOn ℝ ∞ b (jetSection F ⁻¹' Ω))
    (hc : ContDiffOn ℝ ∞ c (jetSection F ⁻¹' Ω))
    (hk : ContDiffOn ℝ ∞ k (jetSection F ⁻¹' Ω))
    (hboundary : ∀ x ∈ K ∩ C₀,
      0 < ((coordDeriv dy (coordDeriv dx F) x ⬝ᵥ normalize (realSecondForm F dy dy x)) * b x +
        Real.sqrt (realSecondForm F dy dy x ⬝ᵥ realSecondForm F dy dy x) * c x)^2 + k x*b x^2) :
    ∃ W : Set Base, IsOpen W ∧ C₀ ⊆ W ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ K ∩ W, ∀ θ : ℝ, |θ| < ε →
        0 < normalInvariant (surfaceFrozenFirst F a e₁ e₂) (surfaceFrozenSize F a e₁ e₂) b c k (x,θ) := by
  let V : Set Base := jetSection F ⁻¹' Ω
  have hσ := jetSection_smooth hF
  have hV : IsOpen V := Ω.isOpen.preimage hσ.continuous
  have hKV : K ⊆ V := fun x hx => hKΩ (mem_image_of_mem _ hx)
  have hmaps : MapsTo (jetSection F) V Ω := fun _ hx => hx
  have hD : ∀ x ∈ V, gramDet (coordDeriv dy F x) (coordDeriv dy (coordDeriv dy F) x) ≠ 0 :=
    fun x hx => preferredJetDomain_velocity_gram (hΩ hx).1
  have hv : ContDiffOn ℝ ∞ (fun x => jetNormal (jetSection F x)) V :=
    (jetNormal_smooth (fun j hj => preferredJetDomain_velocity_gram (hΩ hj).1)).comp hσ.contDiffOn hmaps
  have hnonzero : ∀ x ∈ V, jetNormal (jetSection F x) ≠ 0 ∨ a x ≠ 0 :=
    fun _ hx => (hΩ hx).2
  have hx := (contDiff_real_coordDeriv hF dx).contDiffOn (s := V)
  have hy := (contDiff_real_coordDeriv hF dy).contDiffOn (s := V)
  have hyy := (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy).contDiffOn (s := V)
  apply zero_amplitude_invariant_collar hK hC₀ hV hKV hx hy hyy hv ha.contDiffOn
    (h₁.comp hσ.contDiffOn hmaps) (h₂.comp hσ.contDiffOn hmaps) hb hc hk hD hnonzero
    (fun _ _ => rfl) (fun x hx => hframe (jetSection F x) hx) hzero
  · intro x hxc
    filter_upwards [(hB.preimage hσ.continuous).mem_nhds (hCB (mem_image_of_mem _ hxc.2))] with y hy
    exact hBadapt _ hy
  · exact hboundary

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
