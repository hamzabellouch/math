import OAI.Analysis.CircleDomains.Sobolev.PotentialPhysicalSmoothing
import OAI.Analysis.CircleDomains.Sobolev.LocalizedPotentialSmoothing
import OAI.Analysis.CircleDomains.Sobolev.RefinedPhysicalSampling
import OAI.Analysis.CircleDomains.Sobolev.PhysicalPartitionBands
import OAI.Analysis.CircleDomains.Topology.RelativePlateauNeighborhoods

namespace OAI

/-! Exact plateaus and bands with both global and localized gradient estimates. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

theorem potential_physical_smoothing_with_localized_plateaus
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
    (S : Set EuclideanPlane) (hS : S ⊆ physicalPlaneDomain d.physicalDomain)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    let Ω := physicalPlaneOpens d.physicalDomain hG
    ∃w : EuclideanPlane → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) w Ω ∧ (∀x ∈ Ω, w x ∈ Icc 0 1) ∧
      (∀x ∈ A₀, w x = 0) ∧ (∀x ∈ A₁, w x = 1) ∧
      (∀i : Fin 2,
        MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ∧
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ≤
          ε + eLpNorm (fun x : EuclideanPlane => (4 * (9 * C)) *
            ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2))) 2 volume ∧
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict S) ≤
          ε + eLpNorm (fun x : EuclideanPlane => (4 * (9 * C)) *
            ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2)))
              2 (volume.restrict S)) ∧
      ∀s ∈ d.dust, s ∈ closure d.quotientDomain →
        liminf u (𝓝[d.quotientDomain] s) ≤
          liminf (quotientPlaneRepresentative d w) (𝓝[d.quotientDomain] s) ∧
        limsup (quotientPlaneRepresentative d w) (𝓝[d.quotientDomain] s) ≤
          limsup u (𝓝[d.quotientDomain] s) := by
  let Ω := physicalPlaneOpens d.physicalDomain hG
  let P : Ω → Set EuclideanPlane := fun x =>
    relativePlateauNeighborhood Ω A₀ V₀ x ∩ relativePlateauNeighborhood Ω A₁ V₁ x
  have hP (x : Ω) : IsOpen (P x) :=
    (isOpen_relativePlateauNeighborhood hA₀ hV₀ x).inter (isOpen_relativePlateauNeighborhood hA₁ hV₁ x)
  have hxP (x : Ω) : x.val ∈ P x :=
    ⟨self_mem_relativePlateauNeighborhood hA₀V₀ x.property, self_mem_relativePlateauNeighborhood hA₁V₁ x.property⟩
  obtain ⟨ι, hι, ρ, center, a, b, c, e, hlt, hphys, hsub, hpair, hdiam, hrefine⟩ :=
    exists_refined_physical_sampling_partition d hG hdisj π hπ he hB hne P hP hxP
  let : Countable ι := hι
  have hv : ∀y (hy : y ∈ d.physicalDomain),
      (u ∘ π) y = u (d.domainEquiv ⟨y, hy⟩).val := by
    intro y hy
    rw [he]
    rfl
  obtain ⟨w, hw, hunit, hinter, henergyw⟩ :=
    potential_positive_partition_smoothing_with_local_energy d hdisj ν N u hu g hg henergy
      m hm hpath (u ∘ π) hv ρ a b c e (fun j => (hlt j).1) (fun j => (hlt j).2)
      hphys hsub hdiam C hC hderiv S hS hε
  let W : ι → Set EuclideanPlane := fun j =>
    euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j))
  have hclosed (j : ι) : W j ⊆
      euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)) := by
    intro x hx
    exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, ⟨hx.2.1.le, hx.2.2.le⟩⟩
  have hsample₀ : ∀j, W j ⊆ relativePlateauNeighborhood Ω A₀ V₀ (center j) :=
    fun j => ((hclosed j).trans (hrefine j)).trans inter_subset_left
  have hsample₁ : ∀j, W j ⊆ relativePlateauNeighborhood Ω A₁ V₁ (center j) :=
    fun j => ((hclosed j).trans (hrefine j)).trans inter_subset_right
  refine ⟨w, hw, hunit, ?_, ?_, henergyw, ?_⟩
  · exact interval_smoothing_eq_on_plateau ρ W (fun x => u (π (planeSphere x))) w A₀ V₀ 0
      hA₀Ω hzero (partition_samples_within_relative_plateau ρ W (fun j => center j) A₀ V₀ hsub hsample₀) hinter
  · exact interval_smoothing_eq_on_plateau ρ W (fun x => u (π (planeSphere x))) w A₁ V₁ 1
      hA₁Ω hone (partition_samples_within_relative_plateau ρ W (fun j => center j) A₁ V₁ hsub hsample₁) hinter
  · exact physical_partition_band_inclusion d hG π he hinf hinfB ρ a b c e
      hphys hsub hpair u hu w hinter

end CircleDomainRigidity

end

end OAI
