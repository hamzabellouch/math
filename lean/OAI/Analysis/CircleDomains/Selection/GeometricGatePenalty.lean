import OAI.Analysis.CircleDomains.Topology.GatePenaltySeparation
import OAI.Analysis.CircleDomains.Topology.SafeGateNeighborhood

namespace OAI

/-! Finite-gate penalties for a domain map and nested target gates. Compact
separation supplies a penalty region disjoint from the retained compact sets. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_geometric_gate_penalty
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (ν : Measure Sphere)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (E H : Set Sphere) (hE : IsClosed E) (k : ℕ) (C : ℕ → Set Sphere)
    (hC : ∀j ≤ k, IsCompact (C j)) (hCU : ∀j ≤ k, C j ⊆ d.quotientDomain)
    (hEC : ∀j ≤ k, Disjoint E (C j))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hg₂ : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞) (m : Sphere → ℝ≥0∞)
    (hgood : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ E → Γ.1.val ⊤ ∈ H →
      (∀j ≤ k, GateRule (C j) (Subtype.val '' (f ⁻¹' W₂)) Γ.1.val) →
      ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1) :
    ∃O : Set Sphere, ∃g₁ : Sphere → ℝ≥0∞,
      IsOpen O ∧ closure O ⊆ d.quotientDomain ∧ Disjoint E (closure O) ∧
      (∀x : d.quotientDomain, x.val ∈ closure O → f x ∉ W₁) ∧
      Measurable g₁ ∧ (∀y, g y ≤ g₁ y) ∧ (∀y, π y ∉ O → g₁ y = g y) ∧
      (∫⁻y, g₁ y ^ 2 ∂sphericalArea) < ∞ ∧
      ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
        Γ.1.val ⊥ ∈ E → Γ.1.val ⊤ ∈ H →
          ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g₁ m Γ.1 := by
  let K : ℕ → Set Sphere := fun _ => Subtype.val '' (f ⁻¹' W₂)
  have hK : ∀j ≤ k, IsOpen (K j) := fun _ _ =>
    hU.isOpenMap_subtype_val _ (hW₂.preimage hf)
  let F := finiteGateForbiddenSet k C K
  have hF : IsCompact F := isCompact_finiteGateForbiddenSet k C K hC hK
  have hFU : F ⊆ d.quotientDomain := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hCU i.val (by omega) hi.1
  have hEF : Disjoint E F := by
    apply Set.disjoint_left.mpr
    intro x hxE hxF
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxF
    exact Set.disjoint_left.mp (hEC i.val (by omega)) hxE hi.1
  have hFQ (x : d.quotientDomain) (hx : x.val ∈ F) : f x ∉ W₁ := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    intro h
    exact hi.2 ⟨x, hW₁₂ h, rfl⟩
  obtain ⟨S, hSo, hFS, hSU, hES, hSW⟩ := exists_safe_gate_neighborhood
    d.quotientDomain E F hU hE hF hFU hEF f hf W₁ hW₁ hFQ
  obtain ⟨O, g₁, hOo, hOS, hg₁, hgg₁, hoff, henergy, hlower⟩ :=
    exists_ungated_half_separation d hU π hπ he ν N E H k C K hC hK S hSo
      (subset_closure.trans hSU) hFS (hES.mono_right subset_closure) g hg hg₂ m hgood
  exact ⟨O, g₁, hOo, hOS.trans (subset_closure.trans hSU),
    hES.mono_right (hOS.trans subset_closure), fun x hx => hSW x (subset_closure (hOS hx)),
    hg₁, hgg₁, hoff, henergy, hlower⟩

end CircleDomainRigidity

end

end OAI
