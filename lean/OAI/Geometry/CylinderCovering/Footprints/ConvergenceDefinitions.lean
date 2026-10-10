import OAI.Geometry.CylinderCovering.Footprints.FootprintsDefinitions
import OAI.Geometry.CylinderCovering.Radial.RiemannDefinitions

namespace OAI

noncomputable section
namespace RadialFootprints
open Set MeasureTheory Filter
open scoped Topology
open CylinderCovering.RadialRiemann

def AbsoluteConvergenceStatement : Prop :=
  ∀ {a b : ℝ}, a < b →
    ∀ {R W : ℝ → ℝ}, ContinuousOn R (Icc a b) → ContinuousOn W (Icc a b) →
    (∀ t ∈ Icc a b, 0 ≤ R t) → ∀ {A B : ℝ}, 0 ≤ A → 0 ≤ B →
    ∀ (tag shear : (N : ℕ) → Fin N → ℝ), (∀ N, IsTagged a b N (tag N)) →
    Tendsto (fun N => ∑ i : Fin N,
      volume.real (absoluteFootprint A B (capMax R a b N i) (step a b N) (shear N i)) *
        W (tag N i)) atTop (𝓝 ((1/2 : ℝ) * ∫ t in a..b, R t^2 * W t))

def AffineConvergenceStatement : Prop :=
  ∀ {a b : ℝ}, a < b →
    ∀ {R W : ℝ → ℝ}, ContinuousOn R (Icc a b) → ContinuousOn W (Icc a b) →
    (∀ t ∈ Icc a b, 0 ≤ R t) → ∀ {A B : ℝ}, 0 ≤ A → A/2 ≤ B →
    ∀ (tag shear : (N : ℕ) → Fin N → ℝ), (∀ N, IsTagged a b N (tag N)) →
    Tendsto (fun N => ∑ i : Fin N,
      volume.real (affineFootprint A B (capMax R a b N i) (step a b N) (shear N i)) *
        W (tag N i)) atTop (𝓝 ((1/2 : ℝ) * ∫ t in a..b, R t^2 * W t))

def HalfheightConvergenceStatement : Prop :=
  ∀ {a b : ℝ}, a < b →
    ∀ {R W : ℝ → ℝ}, ContinuousOn R (Icc a b) → ContinuousOn W (Icc a b) →
    (∀ t ∈ Icc a b, 0 ≤ R t) → ∀ {E : ℝ}, 0 ≤ E →
    ∀ (tag shear : (N : ℕ) → Fin N → ℝ), (∀ N, IsTagged a b N (tag N)) →
    Tendsto (fun N => ∑ i : Fin N,
      volume.real (halfheightFootprint (step a b N / 2) (E * step a b N)
        (capMax R a b N i) (shear N i)) * W (tag N i))
      atTop (𝓝 ((1/2 : ℝ) * ∫ t in a..b, R t^2 * W t))

def FootprintConvergenceStatement : Prop :=
  AbsoluteConvergenceStatement ∧ AffineConvergenceStatement ∧ HalfheightConvergenceStatement

end RadialFootprints

end

end OAI
