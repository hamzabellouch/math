import OAI.Analysis.CircleDomains.Topology.SeparatingChainPotential
import OAI.Analysis.CircleDomains.Selection.GeometricGatePenalty

namespace OAI

/-! Combine the proved finite-gate penalty with the actual chain-distance
construction. This is the bounded raw barrier, before Sobolev regularization
and the compatibility argument for the new smooth coordinate. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_raw_gated_barrier
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (hUB : Disjoint d.quotientDomain B) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (E H : Set Sphere) (hE : IsClosed E) (hH : IsClosed H)
    (hEU : E ⊆ d.quotientDomain) (hHU : H ⊆ d.quotientDomain)
    (k : ℕ) (C : ℕ → Set Sphere)
    (hC : ∀j ≤ k, IsCompact (C j)) (hCU : ∀j ≤ k, C j ⊆ d.quotientDomain)
    (hEC : ∀j ≤ k, Disjoint E (C j))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (hgood : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ E → Γ.1.val ⊤ ∈ H →
      (∀j ≤ k, GateRule (C j) (Subtype.val '' (f ⁻¹' W₂)) Γ.1.val) →
      ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1)
    (hBU : Bᶜ ⊆ d.quotientDomain) (hm₂ : (∑' x, m x ^ 2) ≠ ∞) :
    ∃O : Set Sphere, ∃g₁ : Sphere → ℝ≥0∞, ∃u : Sphere → ℝ,
      IsOpen O ∧ closure O ⊆ d.quotientDomain ∧ Disjoint E (closure O) ∧
      (∀x : d.quotientDomain, x.val ∈ closure O → f x ∉ W₁) ∧
      Measurable g₁ ∧ (∀y, g y ≤ g₁ y) ∧ (∀y, π y ∉ O → g₁ y = g y) ∧
      (∫⁻y, g₁ y ^ 2 ∂sphericalArea) < ∞ ∧
      (∀x, u x ∈ Icc 0 1) ∧ (∀x ∈ E, u x = 0) ∧ (∀x ∈ H, u x = 1) ∧
      (∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
        Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
        ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g₁ m Γ.1) ∧
      ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
        liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s := by
  obtain ⟨O, g₁, hOo, hOU, hEO, hOW, hg₁, hgg₁, hoff, henergy, hlower⟩ :=
    exists_geometric_gate_penalty d hU π hπ he ν N E H hE k C hC hCU hEC
      f hf W₁ W₂ hW₁ hW₂ hW₁₂ g hg henergy m hgood
  let S := (E ∪ H)ᶜ
  have hSo : IsOpen S := (hE.union hH).isOpen_compl
  have hBS : B ⊆ S := by
    intro s hs hmem
    rcases hmem with hsE | hsH
    · exact Set.disjoint_left.mp hUB (hEU hsE) hs
    · exact Set.disjoint_left.mp hUB (hHU hsH) hs
  have hFE : frontier E ⊆ d.quotientDomain := by
    exact frontier_subset_closure.trans (by simpa only [hE.closure_eq] using hEU)
  have hFH : frontier H ⊆ d.quotientDomain := by
    exact frontier_subset_closure.trans (by simpa only [hH.closure_eq] using hHU)
  obtain ⟨u, hub, huE, huH, hupath, huband⟩ := exists_separating_chain_potential
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N E H hFE hFH g₁ hg₁ henergy m hm w hw (fun z hz => (hpos z hz).trans (hgg₁ z))
    hpoint hlower hBU S hSo hBS hm₂
  exact ⟨O, g₁, u, hOo, hOU, hEO, hOW, hg₁, hgg₁, hoff, henergy, hub,
    fun x hx => huE x ⟨hx, hEU hx⟩, fun x hx => huH x ⟨hx, hHU hx⟩, hupath, huband⟩

end CircleDomainRigidity

end

end OAI
