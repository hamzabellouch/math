import OAI.Analysis.CircleDomains.Topology.CompactExitPenalty
import OAI.Analysis.CircleDomains.Sobolev.BoundedDensityEnergy
import OAI.Analysis.CircleDomains.Probability.ReversedPhysicalOccupation
import OAI.Analysis.CircleDomains.Selection.LastEntryCuts
import OAI.Analysis.CircleDomains.Sobolev.FiniteSphericalArea

namespace OAI

/-! Compactly many forbidden gate hits admit a bounded penalty density in
a safe relatively compact domain region. Adding it preserves finite energy
and leaves the original density unchanged outside that region. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_gate_penalty_density
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (F S : Set Sphere) (hF : IsCompact F) (hS : IsOpen S) (hFS : F ⊆ S)
    (hSU : S ⊆ d.quotientDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hg₂ : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞) :
    ∃O : Set Sphere, ∃g₁ : Sphere → ℝ≥0∞,
      IsOpen O ∧ F ⊆ O ∧ closure O ⊆ S ∧ Measurable g₁ ∧
      (∀y, g y ≤ g₁ y) ∧ (∀y, π y ∉ O → g₁ y = g y) ∧
      (∫⁻y, g₁ y ^ 2 ∂sphericalArea) < ∞ ∧
      ∀γ : FinitePhysicalPath d.domainEquiv d.basePoint,
        γ.val ⊥ ∉ O → γ.val ⊤ ∈ F → ∀m : Sphere → ℝ≥0∞,
          1 ≤ physicalTollCost d g₁ m γ := by
  obtain ⟨O, hOo, hFO, hOS⟩ := hF.exists_isOpen_closure_subset (hS.mem_nhdsSet.mpr hFS)
  have hOU : closure O ⊆ d.quotientDomain := hOS.trans hSU
  let A := π ⁻¹' F
  have hA : IsCompact A := (hF.isClosed.preimage hπ).isCompact
  obtain ⟨h, C, hh, hC, hbound, hzero, hpay⟩ := exists_compact_exit_penalty
    d hU π hπ he O hOo hOU A hA (preimage_mono hFO)
  let g₁ : Sphere → ℝ≥0∞ := fun y => g y + h y
  refine ⟨O, g₁, hOo, hFO, hOS, hg.add hh, fun y => le_self_add, ?_, ?_, ?_⟩
  · intro y hy
    change g y + h y = g y
    rw [hzero y hy, add_zero]
  · exact lintegral_add_sq_lt_top_of_bounded sphericalArea g h hg hg₂ C hC hbound
  · intro γ hstart hend m
    let ρ := reversedFinitePhysicalPath d.domainEquiv d.basePoint γ
    have hρ0 : ρ.val ⊥ ∈ O := by
      change reversedPath γ.val ⊥ ∈ O
      rw [reversedPath_zero]
      exact hFO hend
    have hρ1 : ρ.val ⊤ ∉ O := by
      change reversedPath γ.val ⊤ ∉ O
      rwa [reversedPath_one]
    have hρA : (d.domainEquiv.symm ⟨ρ.val ⊥, hOU (subset_closure hρ0)⟩).val ∈ A := by
      change π (d.domainEquiv.symm ⟨ρ.val ⊥, _⟩).val ∈ F
      rw [← he]
      simp only [Homeomorph.apply_symm_apply]
      change reversedPath γ.val ⊥ ∈ F
      rwa [reversedPath_zero]
    have hp := hpay ρ hρ0 hρ1 hρA m
    rw [physicalTollCost_reversed] at hp
    apply hp.trans
    apply add_le_add _ le_rfl
    apply lintegral_mono
    intro y
    change h y ≤ g y + h y
    calc
      h y = 0 + h y := (zero_add _).symm
      _ ≤ g y + h y := add_le_add bot_le le_rfl

end CircleDomainRigidity

end

end OAI
