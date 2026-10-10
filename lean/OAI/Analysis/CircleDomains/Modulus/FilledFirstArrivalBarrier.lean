import OAI.Analysis.CircleDomains.Modulus.FirstArrivalBarrierPotential
import OAI.Analysis.CircleDomains.Selection.FillRegionBands

namespace OAI

/-! The first-arrival barrier can be chosen equal to one throughout a closed
terminal collar while retaining its path inequality and all dust-band bounds. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_filled_first_arrival_barrier_potential
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hUB : Disjoint d.quotientDomain B) (hBU : Bᶜ ⊆ d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (E : Set Sphere) (hE : IsClosed E) (hEU : E ⊆ d.quotientDomain)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π B p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint E (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hm₂ : (∑' x, m x ^ 2) ≠ ∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (hunit : ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) → ρ.val ⊥ ∈ E → ρ.val ⊤ = p →
      (∀t < (⊤ : PathTime), ρ.val t ≠ p) →
      GateRules (fun j => frontier (D j).region)
        (fun _ => Subtype.val '' (f ⁻¹' closure W₂)) ρ.val →
      1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m) :
    ∃k : ℕ, ∃O : Set Sphere, ∃g₁ : Sphere → ℝ≥0∞, ∃u : Sphere → ℝ,
      IsOpen O ∧ closure O ⊆ d.quotientDomain ∧ Disjoint E (closure O) ∧
      (∀x : d.quotientDomain, x.val ∈ closure O → f x ∉ W₁) ∧
      Measurable g₁ ∧ (∀y, g y ≤ g₁ y) ∧ (∀y, π y ∉ O → g₁ y = g y) ∧
      (∫⁻y, g₁ y ^ 2 ∂sphericalArea) < ∞ ∧
      (∀x, u x ∈ Icc 0 1) ∧ (∀x ∈ E, u x = 0) ∧
      (∀x ∈ closure (D k).region, u x = 1) ∧
      (∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
        Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
        ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g₁ m Γ.1) ∧
      ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
        liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s := by
  obtain ⟨k, O, g₁, u, hO, hOU, hEO, hfO, hg₁, hgg₁, hagree, henergy₁,
    hu, huE, huD, hpath, hband⟩ := exists_first_arrival_barrier_potential
      hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hUB hBU
      hdense hinfty hbad ν N E hE hEU p hpDust hp D hnest hshrink hED f hf W₁ W₂
      hW₁ hW₂ hW₁₂ g hg henergy m hm hm₂ w hw hpos hpoint hunit
  have hDo : IsOpen (D k).region := (D k).isOpen_region hπ hclosed hsurj hr
  have hDU : frontier (D k).region ⊆ d.quotientDomain :=
    (D k).frontier_region_subset_quotient d π hπ he hDo
  have ha : Antitone (fun j => (D j).region) :=
    antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  have hEk : Disjoint E (D k).region :=
    hED.mono_right ((ha (Nat.zero_le k)).trans subset_closure)
  refine ⟨k, O, g₁, fillRegionOne (D k).region u, hO, hOU, hEO, hfO,
    hg₁, hgg₁, hagree, henergy₁, fillRegionOne_mem_Icc _ _ hu, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxD : x ∉ (D k).region := fun h => Set.disjoint_left.mp hEk hx h
    simpa only [fillRegionOne, ite_eq_right hxD] using huE x hx
  · intro x hx
    by_cases hxD : x ∈ (D k).region
    · exact ite_eq_left hxD
    · have hxf : x ∈ frontier (D k).region := by
        rw [hDo.frontier_eq]
        exact ⟨hx, hxD⟩
      simpa only [fillRegionOne, ite_eq_right hxD] using huD x hxf
  · exact fillRegionOne_path_inequality d hU ν N (D k).region hDo hDU u huD
      g₁ hg₁ m hpoint hpath
  · intro s hs
    apply fillRegionOne_band d.quotientDomain (D k).region hDo u
      (by simpa only [hdense.closure_eq] using (Set.mem_univ s))
      (fun hf => Set.disjoint_left.mp hUB (hDU hf) hs) (4 * m s)
    exact hband s hs

end CircleDomainRigidity

end

end OAI
