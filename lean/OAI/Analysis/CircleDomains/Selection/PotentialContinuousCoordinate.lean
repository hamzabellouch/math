import OAI.Analysis.CircleDomains.Selection.PotentialPhysicalPlateaus
import OAI.Analysis.CircleDomains.Selection.PhysicalRealCoordinate

namespace OAI

/-! The smoothed barrier is a continuous quotient coordinate with a genuine
smooth, measurable, finite-energy physical representative. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

theorem potential_continuous_physical_coordinate
    (d : PathCodeData X Sphere) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (hG : IsOpen d.physicalDomain)
    (π : Sphere → X) (hπ : Continuous π)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hinf : OnePoint.infty ∈ d.physicalDomain) (hinfB : π OnePoint.infty ∉ d.dust)
    (hB : IsClosed d.dust) (hne : d.dust.Nonempty)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (A₀ V₀ A₁ V₁ : Set EuclideanPlane)
    (hA₀ : IsOpen (physicalPlaneDomain d.physicalDomain \ A₀)) (hV₀ : IsOpen V₀) (hA₀V₀ : A₀ ⊆ V₀)
    (hA₁ : IsOpen (physicalPlaneDomain d.physicalDomain \ A₁)) (hV₁ : IsOpen V₁) (hA₁V₁ : A₁ ⊆ V₁)
    (hA₀Ω : A₀ ⊆ physicalPlaneDomain d.physicalDomain)
    (hA₁Ω : A₁ ⊆ physicalPlaneDomain d.physicalDomain)
    (hzero : ∀x ∈ V₀, u (π (planeSphere x)) = 0)
    (hone : ∀x ∈ V₁, u (π (planeSphere x)) = 1)
    (K : Set EuclideanPlane) (hK : IsCompact K) (hKA₀ : Kᶜ ⊆ A₀)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (w : EuclideanPlane → ℝ) (Q : PhysicalRealCoordinate d π),
      ContDiffOn ℝ (⊤ : ℕ∞) w (physicalPlaneDomain d.physicalDomain) ∧
      Q.quotient = quotientPlaneRepresentative d w ∧
      (∀i : Fin 2, eLpNorm (fun p => (fderiv ℝ Q.physical p)
        (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain)) =
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain))) ∧
      (∀i : Fin 2,
        MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain)) ∧
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain)) ≤
          ε + eLpNorm (fun x : EuclideanPlane => (4 * (9 * C)) *
            ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2))) 2 volume) ∧
      (∀x ∈ A₀, Q.quotient (π (planeSphere x)) = 0) ∧
      (∀x ∈ A₁, Q.quotient (π (planeSphere x)) = 1) ∧
      ∀s ∈ d.dust, s ∈ closure d.quotientDomain →
        liminf u (𝓝[d.quotientDomain] s) ≤ liminf Q.quotient (𝓝[d.quotientDomain] s) ∧
        limsup Q.quotient (𝓝[d.quotientDomain] s) ≤ limsup u (𝓝[d.quotientDomain] s) := by
  obtain ⟨w, hw, hunit, hwzero, hwone, henergyw, hband⟩ :=
    potential_physical_smoothing_with_plateaus d hdisj ν N u hu g hg henergy m hm hpath
      hG π hπ he hinf hinfB hB hne C hC hderiv A₀ V₀ A₁ V₁ hA₀ hV₀ hA₀V₀ hA₁ hV₁ hA₁V₁
      hA₀Ω hA₁Ω hzero hone hε
  obtain ⟨Q, hQ, hnorm⟩ := physicalRealCoordinate_of_plane_smoothing d hG π he w hw hunit
    (fun i => (henergyw i).1) hK (fun x hx => hwzero x (hKA₀ hx))
  refine ⟨w, Q, hw, hQ, hnorm, henergyw, ?_, ?_, ?_⟩
  · intro x hx
    rw [hQ, quotientPlaneRepresentative_plane d w π he (hA₀Ω hx)]
    exact hwzero x hx
  · intro x hx
    rw [hQ, quotientPlaneRepresentative_plane d w π he (hA₁Ω hx)]
    exact hwone x hx
  · simpa only [hQ] using hband

end CircleDomainRigidity

end

end OAI
