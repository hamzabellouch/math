import OAI.Analysis.CircleDomains.Modulus.RawGatedBarrier
import OAI.Analysis.CircleDomains.Topology.FiniteGatedCollarSeparation

namespace OAI

/-! The first-arrival hypothesis gives a bounded separating
potential with controlled dust bands. Finite collar separation, the geometric
gate penalty and all progressively shrinking jumps are constructed here. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_first_arrival_barrier_potential
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
      (∀x ∈ frontier (D k).region, u x = 1) ∧
      (∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
        Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
        ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g₁ m Γ.1) ∧
      ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
        liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s := by
  let K : ℕ → Set Sphere := fun _ => Subtype.val '' (f ⁻¹' closure W₂)
  obtain ⟨k, hk⟩ := exists_finite_gated_collar_cost_lower_bound
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hbad ν N
    E hEU p hpDust hp D hnest hshrink hED K g hg henergy m hm w hw hpos hpoint hunit
  have hDo (j : ℕ) : IsOpen (D j).region := (D j).isOpen_region hπ hclosed hsurj hr
  have hDsub (j : ℕ) : frontier (D j).region ⊆ d.quotientDomain :=
    (D j).frontier_region_subset_quotient d π hπ he (hDo j)
  have ha : Antitone (fun j => (D j).region) :=
    antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  have hEDj (j : ℕ) : Disjoint E (frontier (D j).region) :=
    hED.mono_right (frontier_subset_closure.trans (closure_mono (ha (Nat.zero_le j))))
  have hgood : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ E → Γ.1.val ⊤ ∈ frontier (D k).region →
      (∀j ≤ k, GateRule (frontier (D j).region) (Subtype.val '' (f ⁻¹' W₂)) Γ.1.val) →
      ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1 := by
    intro Γ hΓ hΓ0 hΓ1 hgates
    apply hk Γ hΓ hΓ0 hΓ1
    intro j hj t ht
    exact image_mono (preimage_mono subset_closure) (hgates j hj t ht)
  obtain ⟨O, g₁, u, h⟩ := exists_raw_gated_barrier
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N E (frontier (D k).region) hE isClosed_frontier hEU (hDsub k)
    k (fun j => frontier (D j).region) (fun _ _ => isClosed_frontier.isCompact)
    (fun j _ => hDsub j) (fun j _ => hEDj j) f hf W₁ W₂ hW₁ hW₂ hW₁₂
    g hg henergy m hm w hw hpos hpoint hgood hBU hm₂
  exact ⟨k, O, g₁, u, h⟩

end CircleDomainRigidity

end

end OAI
