import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryNormalMatch
import OAI.Geometry.SurfaceImmersion.Whitney.BoundaryInvariantCollar

namespace OAI

/-! The collar inequality from the old immersion's boundary inequality.
Its collar and shift window are fixed before selecting large turn jets. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes CollarVelocity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem geometric_boundary_collar {K C₀ O Ω : Set E} {J : Set ℝ}
    (hK : IsCompact K) (hC₀ : IsClosed C₀) (hO : IsOpen O) (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) (hOΩ : O ⊆ Ω) (hCcl : C₀ ⊆ closure O) (hJ : IsCompact J)
    {Q X Y C e₁ e₂ : E → Vec} {R b c k : E → ℝ} {β : E × ℝ → ℝ}
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hX : ContDiffOn ℝ ∞ X Ω)
    (hY : ContDiffOn ℝ ∞ Y Ω) (hC : ContDiffOn ℝ ∞ C Ω)
    (hR : ContDiffOn ℝ ∞ R Ω) (h₁ : ContDiffOn ℝ ∞ e₁ Ω)
    (h₂ : ContDiffOn ℝ ∞ e₂ Ω) (hβ : ContDiffOn ℝ ∞ β (Ω ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ b Ω) (hc : ContDiffOn ℝ ∞ c Ω) (hk : ContDiffOn ℝ ∞ k Ω)
    (hD : ∀ x ∈ Ω, gramDet (Y x) (C x) ≠ 0)
    (hframe : ∀ x ∈ Ω, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hR0 : ∀ x ∈ Ω, R x ≠ 0)
    (hproj : ∀ x ∈ Ω, Q x = X x - realNormalPart (Y x) (C x) (X x))
    (hext : ∀ x ∈ O, Q x + R x • direction (e₁ x) (e₂ x) 0 = X x)
    (hzero : ∀ x ∈ K ∩ C₀, ∀ t ∈ J, β (x, t) = 0) (d : E)
    (hboundary : ∀ x ∈ K ∩ C₀,
      0 < ((fderiv ℝ X x d ⬝ᵥ normalize (realNormalPart (X x) (Y x) (C x))) * b x +
        Real.sqrt (realNormalPart (X x) (Y x) (C x) ⬝ᵥ
          realNormalPart (X x) (Y x) (C x)) * c x) ^ 2 + k x * b x ^ 2) :
    ∃ W : Set E, IsOpen W ∧ C₀ ⊆ W ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ K ∩ W, ∀ t ∈ J, ∀ h : ℝ, |h| < ε →
        0 < normalInvariant (frozenFirst Q X Y C R e₁ e₂ d)
          (frozenSize X Y C R e₁ e₂) b c k (x, β (x, t) + h) := by
  obtain ⟨hfirst, hsize⟩ := frozen_coefficients_smoothOn hΩ hQ hX hY hC hR h₁ h₂ hD hframe hR0 d
  apply boundary_invariant_collar hK hC₀ hΩ hKΩ hJ hfirst hsize hβ hb hc hk hzero
  intro x hx
  obtain ⟨hfirst0, hsize0⟩ := boundary_normal_match (α := fun _ => 0)
    hΩ hO hOΩ hQ hX hR h₁ h₂ contDiffOn_const hproj hext
    ⟨hCcl hx.2, hKΩ hx.1⟩ d (hframe x (hKΩ hx.1))
  change 0 < (frozenFirst Q X Y C R e₁ e₂ d (x, 0) * b x +
    frozenSize X Y C R e₁ e₂ (x, 0) * c x) ^ 2 + k x * b x ^ 2
  rw [hfirst0, hsize0]
  exact hboundary x hx

end ClosedSurfaceR4.VelocityFrame

end

end OAI
