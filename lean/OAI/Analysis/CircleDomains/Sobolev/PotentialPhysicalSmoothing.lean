import OAI.Analysis.CircleDomains.Sobolev.PotentialGlobalSmoothing
import OAI.Analysis.CircleDomains.Topology.QuotientFinitePlane
import OAI.Analysis.CircleDomains.Topology.QuotientSamplingBands

namespace OAI

/-! Actual physical-domain smoothing with global energy and all quotient bands. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

theorem potential_physical_smoothing
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
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    let Ω := physicalPlaneOpens d.physicalDomain hG
    ∃w : EuclideanPlane → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) w Ω ∧ (∀x ∈ Ω, w x ∈ Icc 0 1) ∧
      (∀i : Fin 2,
        MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ∧
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ≤
          ε + eLpNorm (fun x : EuclideanPlane => (4 * (9 * C)) *
            ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2))) 2 volume) ∧
      ∀s ∈ d.dust, s ∈ closure d.quotientDomain →
        liminf u (𝓝[d.quotientDomain] s) ≤
          liminf (quotientPlaneRepresentative d w) (𝓝[d.quotientDomain] s) ∧
        limsup (quotientPlaneRepresentative d w) (𝓝[d.quotientDomain] s) ≤
          limsup u (𝓝[d.quotientDomain] s) := by
  let Ω := physicalPlaneOpens d.physicalDomain hG
  let q : EuclideanPlane → X := π ∘ planeSphere
  obtain ⟨ι, hι, ρ, a, b, c, e, hlt, hphys, hsub, hpair, hdiam⟩ :=
    exists_physical_sampling_partition d hG hdisj π hπ he hB hne
  let : Countable ι := hι
  have hv : ∀y (hy : y ∈ d.physicalDomain),
      (u ∘ π) y = u (d.domainEquiv ⟨y, hy⟩).val := by
    intro y hy
    rw [he]
    rfl
  obtain ⟨w, hw, hunit, hinter, henergyw⟩ :=
    potential_positive_partition_smoothing_with_energy d hdisj ν N u hu g hg henergy
      m hm hpath (u ∘ π) hv ρ a b c e (fun j => (hlt j).1) (fun j => (hlt j).2)
      hphys hsub hdiam C hC hderiv hε
  refine ⟨w, hw, hunit, henergyw, ?_⟩
  intro s hs hscl
  have hsne : s ≠ π OnePoint.infty := by
    intro heq
    exact hinfB (heq ▸ hs)
  let U := d.quotientDomain \ {π OnePoint.infty}
  have hnhds : 𝓝[U] s = 𝓝[d.quotientDomain] s :=
    hsne.nhdsWithin_sdiff_singleton d.quotientDomain
  have hsclU : s ∈ closure U := by
    rw [mem_closure_iff_nhdsWithin_neBot, hnhds]
    exact mem_closure_iff_nhdsWithin_neBot.mp hscl
  let W : ι → Set EuclideanPlane := fun j =>
    euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j))
  have hclosed (j : ι) : W j ⊆
      euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)) := by
    intro x hx
    exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, ⟨hx.2.1.le, hx.2.2.le⟩⟩
  have hWO (j : ι) : W j ⊆ Ω := by
    intro x hx
    exact hphys j _ (mk_mem_closedComplexRectangle (hclosed j hx).1 (hclosed j hx).2)
  have hbound := quotient_sampling_band_inclusion (Ω : Set EuclideanPlane) U d.dust q
    ρ.weight W u (quotientPlaneRepresentative d w) w
    (quotient_finite_plane_mapsTo d π he hinf) (quotient_finite_plane_covers d π he)
    (fun x hx => quotientPlaneRepresentative_plane d w π he hx) hWO
    (by
      intro x hx j hj y hy
      exact hpair j x (hclosed j (hsub j (subset_tsupport (ρ.weight j) hj))) y (hclosed j hy))
    hinter hu hs hsclU
  simpa only [hnhds] using hbound

end CircleDomainRigidity

end

end OAI
