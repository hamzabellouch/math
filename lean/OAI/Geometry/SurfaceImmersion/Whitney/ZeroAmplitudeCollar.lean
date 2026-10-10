import OAI.Geometry.SurfaceImmersion.Geometry.ZeroAmplitudeBoundary
import OAI.Geometry.SurfaceImmersion.Whitney.BoundaryInvariantCollar

namespace OAI

/-! The old ordered boundary inequality gives one uniform small-angle collar
before any loop or large transverse derivative is chosen. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes CollarVelocity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem zero_amplitude_invariant_collar {K C₀ Ω : Set E}
    (hK : IsCompact K) (hC₀ : IsClosed C₀) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {X Y C v e₁ e₂ : E → Vec} {a b c k : E → ℝ}
    (hX : ContDiffOn ℝ ∞ X Ω) (hY : ContDiffOn ℝ ∞ Y Ω) (hC : ContDiffOn ℝ ∞ C Ω)
    (hv : ContDiffOn ℝ ∞ v Ω) (ha : ContDiffOn ℝ ∞ a Ω)
    (h₁ : ContDiffOn ℝ ∞ e₁ Ω) (h₂ : ContDiffOn ℝ ∞ e₂ Ω)
    (hb : ContDiffOn ℝ ∞ b Ω) (hc : ContDiffOn ℝ ∞ c Ω) (hk : ContDiffOn ℝ ∞ k Ω)
    (hD : ∀ x ∈ Ω, gramDet (Y x) (C x) ≠ 0)
    (hn : ∀ x ∈ Ω, v x ≠ 0 ∨ a x ≠ 0)
    (hproj : ∀ x ∈ Ω, v x = realNormalPart (Y x) (C x) (X x))
    (hframe : ∀ x ∈ Ω, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hzero : ∀ x ∈ C₀, a x = 0)
    (hadapt : ∀ x ∈ K ∩ C₀, e₁ =ᶠ[𝓝 x] fun y => normalize (v y))
    (d : E)
    (hboundary : ∀ x ∈ K ∩ C₀,
      0 < ((fderiv ℝ X x d ⬝ᵥ normalize (realNormalPart (X x) (Y x) (C x))) * b x +
        Real.sqrt (realNormalPart (X x) (Y x) (C x) ⬝ᵥ
          realNormalPart (X x) (Y x) (C x)) * c x)^2 + k x * b x^2) :
    ∃ W : Set E, IsOpen W ∧ C₀ ⊆ W ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ K ∩ W, ∀ θ : ℝ, |θ| < ε →
        0 < normalInvariant
          (frozenFirst (X-v) X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂ d)
          (frozenSize X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂) b c k (x,θ) := by
  have hR := velocityRadius_smoothOn hv ha hn
  obtain ⟨hfirst,hsize⟩ := frozen_coefficients_smoothOn hΩ (hX.sub hv) hX hY hC hR h₁ h₂
    hD hframe (fun x hx => (velocityRadius_pos (hn x hx)).ne') d
  have hbound : ∀ x ∈ K ∩ C₀, 0 < normalInvariant
      (frozenFirst (X-v) X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂ d)
      (frozenSize X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂) b c k (x,0) := by
    intro x hx
    have hxΩ := hKΩ hx.1
    have hxnb := hΩ.mem_nhds hxΩ
    have hn0 : v x ≠ 0 := (hn x hxΩ).resolve_right (not_not_intro (hzero x hx.2))
    obtain ⟨hf,hs⟩ := zero_amplitude_boundary_coefficients (hX.contDiffAt hxnb)
      (hv.contDiffAt hxnb) (ha.contDiffAt hxnb) (h₁.contDiffAt hxnb) (h₂.contDiffAt hxnb)
      hn0 (hzero x hx.2) (hadapt x hx) (hproj x hxΩ) (hframe x hxΩ) d
    change 0 < (_ * b x + _ * c x)^2 + k x * b x^2
    rw [hf,hs]
    exact hboundary x hx
  obtain ⟨W,hW,hCW,ε,hε,hcol⟩ := boundary_invariant_collar (J := {0})
    (D := frozenFirst (X-v) X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂ d)
    (S := frozenSize X Y C (fun y => velocityRadius (v y) (a y)) e₁ e₂)
    (β := fun _ => 0) hK hC₀ hΩ hKΩ (isCompact_singleton)
    hfirst hsize contDiffOn_const hb hc hk (fun _ _ _ _ => rfl) hbound
  refine ⟨W,hW,hCW,ε,hε,?_⟩
  intro x hx θ hθ
  simpa only [zero_add] using hcol x hx 0 (mem_singleton 0) θ hθ

end ClosedSurfaceR4.VelocityFrame

end

end OAI
