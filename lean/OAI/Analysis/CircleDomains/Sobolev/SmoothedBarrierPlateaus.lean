import OAI.Analysis.CircleDomains.Selection.LocalizedContinuousCoordinate
import OAI.Analysis.CircleDomains.Modulus.BarrierPlateauGeometry

namespace OAI

/-! Apply the smoothing construction to the actual anchor and terminal
constant regions, choosing the averaging neighborhoods and compact exterior. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem smooth_barrier_with_anchor_and_terminal
    {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → X) (hπ : Continuous π)
    (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hinf : OnePoint.infty ∈ d.physicalDomain) (hinfB : π OnePoint.infty ∉ d.dust)
    (hB : IsClosed d.dust) (hne : d.dust.Nonempty)
    (E EStar H V : Set X) (hEU : E ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior E)
    (hinfE : π OnePoint.infty ∈ interior E)
    (hH : IsClosed H) (hHV : H ⊆ V)
    (hV : IsOpen V) (hHinf : π OnePoint.infty ∉ H)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1)
    (huE : ∀x ∈ E, u x = 0) (huV : ∀x ∈ V, u x = 1)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞)
    (m : X → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (S : Set EuclideanPlane) (hS : S ⊆ physicalPlaneDomain d.physicalDomain)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (w : EuclideanPlane → ℝ) (Q : PhysicalRealCoordinate d π),
      ContDiffOn ℝ (⊤ : ℕ∞) w (physicalPlaneDomain d.physicalDomain) ∧
      Q.quotient = quotientPlaneRepresentative d w ∧
      (∀x ∈ EStar, Q.quotient x = 0) ∧ (∀x ∈ H ∩ d.quotientDomain, Q.quotient x = 1) ∧
      (∀s ∈ d.dust, s ∈ closure d.quotientDomain →
        liminf u (𝓝[d.quotientDomain] s) ≤ liminf Q.quotient (𝓝[d.quotientDomain] s) ∧
        limsup Q.quotient (𝓝[d.quotientDomain] s) ≤ limsup u (𝓝[d.quotientDomain] s)) ∧
      ∀i : Fin 2,
        MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain)) ∧
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict S) ≤
          ε + eLpNorm (fun x : EuclideanPlane => (4 * (9 * C)) *
            ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2)))
              2 (volume.restrict S) := by
  let F := EStar ∪ {π OnePoint.infty}
  have hF : IsCompact F := hEStar.union isCompact_singleton
  have hFE : F ⊆ interior E := union_subset hEStarE (singleton_subset_iff.mpr hinfE)
  obtain ⟨A, U, hA, hU, hFA, hAU, hUE⟩ := exists_closed_anchor_plateau hF hFE
  let Ω := physicalPlaneDomain d.physicalDomain
  let q := π ∘ planeSphere
  let A₀ := Ω ∩ q ⁻¹' A
  let V₀ := Ω ∩ q ⁻¹' U
  let A₁ := Ω ∩ q ⁻¹' H
  let V₁ := Ω ∩ q ⁻¹' V
  have hΩ : IsOpen Ω := isOpen_physicalPlaneDomain hG
  have hq : Continuous q := hπ.comp continuous_planeSphere
  have hV₀ : IsOpen V₀ := hΩ.inter (hU.preimage hq)
  have hV₁ : IsOpen V₁ := hΩ.inter (hV.preimage hq)
  have hA₀V₀ : A₀ ⊆ V₀ := fun _ hx => ⟨hx.1, hAU hx.2⟩
  have hA₁V₁ : A₁ ⊆ V₁ := fun _ hx => ⟨hx.1, hHV hx.2⟩
  have hzero : ∀x ∈ V₀, u (π (planeSphere x)) = 0 := fun _ hx => huE _ (hUE hx.2)
  have hone : ∀x ∈ V₁, u (π (planeSphere x)) = 1 := fun _ hx => huV _ hx.2
  have hAVinf : π OnePoint.infty ∈ interior A := hFA (Or.inr rfl)
  have hnhds : d.physicalDomain ∩ π ⁻¹' interior A ∈ 𝓝 OnePoint.infty :=
    (hG.inter (isOpen_interior.preimage hπ)).mem_nhds ⟨hinf, hAVinf⟩
  obtain ⟨K, hK, houtside⟩ := exists_compact_plane_exterior_of_nhds hnhds
  have hKA₀ : Kᶜ ⊆ A₀ := by
    intro x hx
    refine ⟨(houtside x hx).1, ?_⟩
    change π (planeSphere x) ∈ A
    exact interior_subset (show π (planeSphere x) ∈ interior A from (houtside x hx).2)
  obtain ⟨w, Q, hw, hQ, _, hnorm, hQ₀, hQ₁, hband⟩ :=
    potential_continuous_physical_coordinate_localized d hdisj ν N u hu g hg henergy m hm hpath
      hG π hπ he hinf hinfB hB hne C hC hderiv A₀ V₀ A₁ V₁
      (physical_plateau_relative_complement_open hG hπ hA) hV₀ hA₀V₀
      (physical_plateau_relative_complement_open hG hπ hH) hV₁ hA₁V₁
      inter_subset_left inter_subset_left hzero hone K hK hKA₀ S hS hε
  refine ⟨w, Q, hw, hQ, ?_, ?_, hband, fun i => ⟨(hnorm i).1, (hnorm i).2.2⟩⟩
  · intro x hx
    by_cases hxi : x = π OnePoint.infty
    · rw [hxi, hQ, ← he ⟨OnePoint.infty, hinf⟩,
        quotientPlaneRepresentative_on_domain d w OnePoint.infty hinf]
      simp [sphereFromPlaneFunction]
    · have hxU : x ∈ d.quotientDomain := hEU (interior_subset (hEStarE hx))
      obtain ⟨z, hz, hzq⟩ := quotient_finite_plane_covers d π he ⟨hxU, by simpa using hxi⟩
      change π (planeSphere z) = x at hzq
      rw [← hzq]
      apply hQ₀ z
      refine ⟨hz, ?_⟩
      change π (planeSphere z) ∈ A
      rw [hzq]
      exact interior_subset (hFA (Or.inl hx))
  · intro x hx
    have hxU := hx.2
    have hxi : x ≠ π OnePoint.infty := fun heq => hHinf (heq ▸ hx.1)
    obtain ⟨z, hz, hzq⟩ := quotient_finite_plane_covers d π he ⟨hxU, by simpa using hxi⟩
    change π (planeSphere z) = x at hzq
    rw [← hzq]
    apply hQ₁ z
    refine ⟨hz, ?_⟩
    change π (planeSphere z) ∈ H
    simpa only [hzq] using hx.1

end CircleDomainRigidity

end

end OAI
