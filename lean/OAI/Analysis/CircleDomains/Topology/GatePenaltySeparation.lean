import OAI.Analysis.CircleDomains.Probability.GatePenaltyDensity
import OAI.Analysis.CircleDomains.Selection.FiniteGateObstacles

namespace OAI

/-! Step 2 of the compatible-barrier construction: replace the finitely many
gate restrictions by a bounded penalty. Good paths retain the original
half-unit separation; every bad path pays at least one unit. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_ungated_half_separation
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (ν : Measure Sphere)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (E H : Set Sphere) (k : ℕ) (C K : ℕ → Set Sphere)
    (hC : ∀j ≤ k, IsCompact (C j)) (hK : ∀j ≤ k, IsOpen (K j))
    (S : Set Sphere) (hS : IsOpen S) (hSU : S ⊆ d.quotientDomain)
    (hFS : finiteGateForbiddenSet k C K ⊆ S) (hES : Disjoint E S)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hg₂ : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞) (m : Sphere → ℝ≥0∞)
    (hgood : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ E → Γ.1.val ⊤ ∈ H → (∀j ≤ k, GateRule (C j) (K j) Γ.1.val) →
      ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1) :
    ∃O : Set Sphere, ∃g₁ : Sphere → ℝ≥0∞,
      IsOpen O ∧ closure O ⊆ S ∧ Measurable g₁ ∧
      (∀y, g y ≤ g₁ y) ∧ (∀y, π y ∉ O → g₁ y = g y) ∧
      (∫⁻y, g₁ y ^ 2 ∂sphericalArea) < ∞ ∧
      ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
        Γ.1.val ⊥ ∈ E → Γ.1.val ⊤ ∈ H →
          ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g₁ m Γ.1 := by
  obtain ⟨O, g₁, hOo, _, hOS, hg₁, hgg₁, hoff, henergy, hpay⟩ :=
    exists_gate_penalty_density d hU π hπ he (finiteGateForbiddenSet k C K) S
      (isCompact_finiteGateForbiddenSet k C K hC hK) hS hFS hSU g hg hg₂
  refine ⟨O, g₁, hOo, hOS, hg₁, hgg₁, hoff, henergy, ?_⟩
  intro Γ hΓ hΓ0 hΓ1
  by_cases hgates : ∀j ≤ k, GateRule (C j) (K j) Γ.1.val
  · apply (hgood Γ hΓ hΓ0 hΓ1 hgates).trans
    exact add_le_add (lintegral_mono hgg₁) le_rfl
  · obtain ⟨t, ht⟩ := exists_forbidden_hit_of_not_finiteGateRules k C K Γ.1.val hgates
    have htpos : (⊥ : PathTime) < t := by
      apply bot_lt_iff_ne_bot.mpr
      intro heq
      exact Set.disjoint_left.mp hES hΓ0 (heq ▸ hFS ht)
    let ρ := affineFinitePhysicalPath d.domainEquiv hU d.basePoint Γ.1 htpos
    have hρ0 : ρ.val ⊥ ∉ O := by
      change Γ.1.val (affinePathTime ⊥ t ⊥) ∉ O
      rw [affinePathTime_zero]
      intro h
      exact Set.disjoint_left.mp hES hΓ0 (hOS (subset_closure h))
    have hρ1 : ρ.val ⊤ ∈ finiteGateForbiddenSet k C K := by
      change Γ.1.val (affinePathTime ⊥ t ⊤) ∈ _
      rwa [affinePathTime_one]
    have hp := hpay ρ hρ0 hρ1 m
    have hwhole : (1 : ℝ≥0∞) ≤ physicalTollCost d g₁ m Γ.1 :=
      hp.trans (physicalTollCost_affine_le d hU Γ.1 htpos g₁ hg₁ m)
    exact (show ENNReal.ofReal ((1 : ℝ)/2) ≤ 1 by norm_num).trans hwhole

end CircleDomainRigidity

end

end OAI
