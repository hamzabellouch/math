import OAI.Analysis.CircleDomains.Selection.FirstEntryRange
import OAI.Analysis.CircleDomains.Probability.ReversedPhysicalOccupation
import OAI.Analysis.CircleDomains.Topology.AllowedPathReversal
import OAI.Analysis.CircleDomains.Selection.LastEntryCuts
import OAI.Analysis.CircleDomains.Selection.ChainPotentialBands

namespace OAI

/-! Filling the terminal collar with the constant value one preserves the
true-path cost inequality. At dust points away from its boundary, the band
is either unchanged or collapses to the constant value. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*}

def fillRegionOne (V : Set X) (u : X → ℝ) (x : X) : ℝ := by
  classical
  exact if x ∈ V then 1 else u x

theorem fillRegionOne_mem_Icc (V : Set X) (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1) (x : X) :
    fillRegionOne V u x ∈ Icc 0 1 := by
  by_cases hx : x ∈ V
  · simp [fillRegionOne, hx]
  · simpa only [fillRegionOne, ite_eq_right hx] using hu x

variable {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem one_sided_cost_to_constant_frontier
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (V : Set X) (hV : IsOpen V) (hfront : frontier V ⊆ d.quotientDomain)
    (u : X → ℝ) (hone : ∀x ∈ frontier V, u x = 1)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (hineq : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hx : Γ.1.val ⊥ ∈ d.quotientDomain)
    (hstart : Γ.1.val ⊥ ∉ V) (hend : Γ.1.val ⊤ ∈ V) :
    ENNReal.ofReal |1 - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1 := by
  by_cases hcl : Γ.1.val ⊥ ∈ closure V
  · have hf : Γ.1.val ⊥ ∈ frontier V := by
      rw [hV.frontier_eq]
      exact ⟨hcl, hstart⟩
    rw [hone _ hf, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact bot_le
  · obtain ⟨ρ, hρ, hρ0, hρ1, _, _, hcost⟩ := exists_allowed_first_entry_prefix_with_range
      d hU ν N Γ hΓ hV hcl (subset_closure hend) g hg m hpoint
    have hi := hineq ρ hρ (hρ0.symm ▸ hx) (hfront hρ1)
    rw [hone _ hρ1, hρ0] at hi
    exact hi.trans (mul_le_mul' le_rfl hcost)

theorem fillRegionOne_path_inequality
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (V : Set X) (hV : IsOpen V) (hfront : frontier V ⊆ d.quotientDomain)
    (u : X → ℝ) (hone : ∀x ∈ frontier V, u x = 1)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (hineq : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hx : Γ.1.val ⊥ ∈ d.quotientDomain) (hy : Γ.1.val ⊤ ∈ d.quotientDomain) :
    ENNReal.ofReal |fillRegionOne V u (Γ.1.val ⊤) - fillRegionOne V u (Γ.1.val ⊥)| ≤
      4 * physicalTollCost d g m Γ.1 := by
  by_cases h0 : Γ.1.val ⊥ ∈ V
  · by_cases h1 : Γ.1.val ⊤ ∈ V
    · simp [fillRegionOne, h0, h1]
    · let Δ := reversedTaggedPhysicalPath d Γ
      have hΔ : AllowedTaggedPath d ν N (Δ.1.val, Δ.2) :=
        allowedTaggedPath_reversed d ν N (Γ.1.val, Γ.2) hΓ hpoint
      have hΔ0 : Δ.1.val ⊥ = Γ.1.val ⊤ := reversedPath_zero Γ.1.val
      have hΔ1 : Δ.1.val ⊤ = Γ.1.val ⊥ := reversedPath_one Γ.1.val
      have hi := one_sided_cost_to_constant_frontier d hU ν N V hV hfront u hone g hg m hpoint hineq
        Δ hΔ (hΔ0.symm ▸ hy) (hΔ0.symm ▸ h1) (hΔ1.symm ▸ h0)
      have he : physicalTollCost d g m Δ.1 = physicalTollCost d g m Γ.1 :=
        physicalTollCost_reversed d g m Γ.1
      rw [hΔ0, he] at hi
      simpa only [fillRegionOne, ite_eq_left h0, ite_eq_right h1, abs_sub_comm] using hi
  · by_cases h1 : Γ.1.val ⊤ ∈ V
    · simpa only [fillRegionOne, ite_eq_right h0, ite_eq_left h1] using
        one_sided_cost_to_constant_frontier d hU ν N V hV hfront u hone g hg m hpoint hineq Γ hΓ hx h0 h1
    · simpa only [fillRegionOne, ite_eq_right h0, ite_eq_right h1] using hineq Γ hΓ hx hy

end CircleDomainRigidity

end

end OAI
