import OAI.Geometry.CylinderCovering.Cartesian.DomainDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering

def CartesianApertureStatement : Prop :=
  ∀ τ η : ℝ, τ ∈ Set.Icc (0 : ℝ) (1/4) → η ∈ Set.Ioc (0 : ℝ) 1 →
    ContinuousOn (CartesianCaps.cap τ η) (Set.Icc (-1 : ℝ) 1) ∧
    (∀ q ∈ Set.Icc (-1 : ℝ) 1,
      CartesianCaps.cap τ η q ∈ Set.Icc (1/2 : ℝ) (3/4) ∧
      CartesianCaps.residual τ η q (CartesianCaps.cap τ η q) = 0 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, CartesianCaps.residual τ η q s = 0 →
        s = CartesianCaps.cap τ η q) ∧
      |CartesianCaps.cap τ η q - (1/2 + τ^2 * (CartesianCaps.d q + η))| ≤ 12 * τ^4 ∧
      ∀ b ∈ Set.Icc (3/4 : ℝ) 1,
        CartesianCaps.aperture τ η b q = Set.Icc 0 (CartesianCaps.cap τ η q)) ∧
    ∀ b ∈ Set.Icc (3/4 : ℝ) 1,
      IsCompact (CartesianCaps.domain τ η b) ∧
      CartesianCaps.domain τ η b = {p : ℝ×ℝ | ∃ q ∈ Set.Icc (-1 : ℝ) 1,
        ∃ s ∈ Set.Icc (0 : ℝ) (CartesianCaps.cap τ η q), p = (q*s,s)} ∧
      1/4 + τ^2 * (1/30 + η) ≤ MeasureTheory.volume.real (CartesianCaps.domain τ η b) ∧
      MeasureTheory.volume.real (CartesianCaps.domain τ η b) ≤
        1/4 + τ^2 * (1/30 + η) + (81/8)*τ^4

end CylinderCovering

end

end OAI
