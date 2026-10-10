import OAI.Geometry.CylinderCovering.Footprints.ProjectionDefinitions
import OAI.Geometry.CylinderCovering.Radial.RiemannDefinitions

namespace OAI

noncomputable section
namespace RadialFootprints
open Set MeasureTheory Filter TriangularCovering
open scoped Topology InnerProductSpace
open CylinderCovering.RadialRiemann

def AbsolutePhysicalConvergenceStatement : Prop :=
  ∀ {α β : ℝ}, α < β →
    ∀ {e : Space}, ‖e‖ = 1 → ∀ (p₀ a b : Space),
    inner ℝ e a = 0 → inner ℝ e b = 0 →
    ∀ {R : ℝ → ℝ} {w : ℝ → Space}, ContinuousOn R (Icc α β) →
    (∀ t ∈ Icc α β, 0 ≤ R t) → ContinuousOn w (Icc α β) →
    (∀ t ∈ Icc α β, inner ℝ e (w t) = 0) →
    ∀ {A B : ℝ}, 0 ≤ A → 0 ≤ B →
    ∀ (tag shear : (N : ℕ) → Fin N → ℝ), (∀ N, IsTagged α β N (tag N)) →
    Tendsto (fun N => ∑ i : Fin N,
      area (projectedCoordinateFootprint e (w (tag N i)) p₀ a b
        (absoluteFootprint A B (capMax R α β N i) (step α β N) (shear N i)))) atTop
      (𝓝 (Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b)^2) *
        ∫ t in α..β, R t^2 / (2 * Real.sqrt (1 + ‖w t‖^2))))

def AffinePhysicalConvergenceStatement : Prop :=
  ∀ {α β : ℝ}, α < β →
    ∀ {e : Space}, ‖e‖ = 1 → ∀ (p₀ a b : Space),
    inner ℝ e a = 0 → inner ℝ e b = 0 →
    ∀ {R : ℝ → ℝ} {w : ℝ → Space}, ContinuousOn R (Icc α β) →
    (∀ t ∈ Icc α β, 0 ≤ R t) → ContinuousOn w (Icc α β) →
    (∀ t ∈ Icc α β, inner ℝ e (w t) = 0) →
    ∀ {A B : ℝ}, 0 ≤ A → A/2 ≤ B →
    ∀ (tag shear : (N : ℕ) → Fin N → ℝ), (∀ N, IsTagged α β N (tag N)) →
    Tendsto (fun N => ∑ i : Fin N,
      area (projectedCoordinateFootprint e (w (tag N i)) p₀ a b
        (affineFootprint A B (capMax R α β N i) (step α β N) (shear N i)))) atTop
      (𝓝 (Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b)^2) *
        ∫ t in α..β, R t^2 / (2 * Real.sqrt (1 + ‖w t‖^2))))

def HalfheightPhysicalConvergenceStatement : Prop :=
  ∀ {α β : ℝ}, α < β →
    ∀ {e : Space}, ‖e‖ = 1 → ∀ (p₀ a b : Space),
    inner ℝ e a = 0 → inner ℝ e b = 0 →
    ∀ {R : ℝ → ℝ} {w : ℝ → Space}, ContinuousOn R (Icc α β) →
    (∀ t ∈ Icc α β, 0 ≤ R t) → ContinuousOn w (Icc α β) →
    (∀ t ∈ Icc α β, inner ℝ e (w t) = 0) →
    ∀ {E : ℝ}, 0 ≤ E →
    ∀ (tag shear : (N : ℕ) → Fin N → ℝ), (∀ N, IsTagged α β N (tag N)) →
    Tendsto (fun N => ∑ i : Fin N,
      area (projectedCoordinateFootprint e (w (tag N i)) p₀ a b
        (halfheightFootprint (step α β N / 2) (E * step α β N)
          (capMax R α β N i) (shear N i)))) atTop
      (𝓝 (Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b)^2) *
        ∫ t in α..β, R t^2 / (2 * Real.sqrt (1 + ‖w t‖^2))))

def PhysicalFootprintConvergenceStatement : Prop :=
  AbsolutePhysicalConvergenceStatement ∧ AffinePhysicalConvergenceStatement ∧
    HalfheightPhysicalConvergenceStatement

end RadialFootprints

end

end OAI
