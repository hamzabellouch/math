import OAI.Analysis.CircleDomains.Selection.AnchorTruncation
import OAI.Analysis.CircleDomains.Topology.ConstantPhysicalPath
import OAI.Analysis.CircleDomains.Modulus.JoinedJunctionCost

namespace OAI

/-! Attach the two outer ends of a limiting block. An anchor containing
the limiting junction is handled by truncation or a common domain point. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_anchor_tail_attachment
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust) (hdense : Dense d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (F H : Set X) (hF : frontier F ⊆ d.quotientDomain) (hH : frontier H ⊆ d.quotientDomain)
    (p : X) (L R J : ℝ≥0∞) (hpaid : m p ≤ J)
    (hleft : p ∈ interior F ∨
      ∃ (α : FinitePhysicalPath d.domainEquiv d.basePoint) (θα : ℕ → TagSlot),
        AllowedTaggedPath d ν N (α.val, θα) ∧ α.val ⊥ ∈ F ∩ d.quotientDomain ∧
        α.val ⊤ = p ∧ interiorPhysicalTollCost d g m α ≤ L)
    (hright : p ∈ interior H ∨
      ∃ (β : FinitePhysicalPath d.domainEquiv d.basePoint) (θβ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (β.val, θβ) ∧ β.val ⊥ ∈ H ∩ d.quotientDomain ∧
        β.val ⊤ = p ∧ interiorPhysicalTollCost d g m β ≤ R) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧
      ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧ ρ.val ⊤ ∈ H ∩ d.quotientDomain ∧
      physicalTollCost d g m ρ ≤ L + R + J := by
  classical
  have hL : L ≤ L + R + J := le_add_right (le_add_right le_rfl)
  have hR : R ≤ L + R + J := le_add_right (le_add_left le_rfl)
  have finish (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot)
      (hρ : AllowedTaggedPath d ν N (ρ.val, θ))
      (hρ0 : ρ.val ⊥ ∈ F ∩ d.quotientDomain) (hρ1 : ρ.val ⊤ ∈ H ∩ d.quotientDomain)
      (hc : interiorPhysicalTollCost d g m ρ ≤ L + R + J) :
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧
        ρ.val ⊤ ∈ H ∩ d.quotientDomain ∧ physicalTollCost d g m ρ ≤ L + R + J := by
    refine ⟨ρ, θ, hρ, hρ0, hρ1, ?_⟩
    rw [← interiorPhysicalTollCost_eq_full d g m ρ (hm _ hρ0.2) (hm _ hρ1.2)]
    exact hc
  have constant (x : X) (hxF : x ∈ F ∩ d.quotientDomain) (hxH : x ∈ H) :
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧
        ρ.val ⊤ ∈ H ∩ d.quotientDomain ∧ physicalTollCost d g m ρ ≤ L + R + J := by
    obtain ⟨ρ, θ, hρ, heq, hc⟩ := exists_allowed_constant_physical_path d hdisj ν N hxF.2
      g m (hm _ hxF.2)
    exact ⟨ρ, θ, hρ, (heq ⊥).symm ▸ hxF, (heq ⊤).symm ▸ ⟨hxH, hxF.2⟩,
      hc.le.trans bot_le⟩
  rcases hleft with hpF | ⟨α, θα, hα, hα0, hα1, hαc⟩
  · rcases hright with hpH | ⟨β, θβ, hβ, hβ0, hβ1, hβc⟩
    · obtain ⟨x, hxU, hxF, hxH⟩ := hdense.exists_mem_open (isOpen_interior.inter isOpen_interior)
        ⟨p, hpF, hpH⟩
      exact constant x ⟨interior_subset hxF, hxU⟩ (interior_subset hxH)
    · by_cases hstart : β.val ⊥ ∈ interior F
      · exact constant (β.val ⊥) ⟨interior_subset hstart, hβ0.2⟩ hβ0.1
      · obtain ⟨σ, hσ, hσ0, hσ1, hσc⟩ := exists_allowed_prefix_to_anchor
          d hU ν N (β, θβ) hβ hF hstart (hβ1.symm ▸ hpF) g hg m hpoint
        obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ :=
          exists_allowed_reversed_interior_cost d ν N σ hσ g m hpoint
        exact finish ρ θ hρ (hρ0.symm ▸ ⟨interior_subset hσ1.1, hσ1.2⟩)
          (hρ1.symm ▸ hσ0.symm ▸ hβ0) (hc.le.trans (hσc.trans (hβc.trans hR)))
  · rcases hright with hpH | ⟨β, θβ, hβ, hβ0, hβ1, hβc⟩
    · by_cases hstart : α.val ⊥ ∈ interior H
      · exact constant (α.val ⊥) hα0 (interior_subset hstart)
      · obtain ⟨ρ, hρ, hρ0, hρ1, hc⟩ := exists_allowed_prefix_to_anchor
          d hU ν N (α, θα) hα hH hstart (hα1.symm ▸ hpH) g hg m hpoint
        exact finish ρ.1 ρ.2 hρ (hρ0.symm ▸ hα0) ⟨interior_subset hρ1.1, hρ1.2⟩
          (hc.trans (hαc.trans hL))
    · obtain ⟨βr, θr, hβr, hβr0, hβr1, hβrc⟩ :=
        exists_allowed_reversed_interior_cost d ν N (β, θβ) hβ g m hpoint
      obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := exists_allowed_joined_junction_cost
        d hU ν N (α, θα) (βr, θr) hα hβr (hα1.trans (hβ1.symm.trans hβr0.symm))
        g hg m hpoint
      apply finish ρ θ hρ (hρ0.symm ▸ hα0) (hρ1.symm ▸ hβr1.symm ▸ hβ0)
      rw [hc, hβrc, hα1]
      exact add_le_add (add_le_add hαc hβc) hpaid

end CircleDomainRigidity

end

end OAI
