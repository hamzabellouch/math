import OAI.Analysis.CircleDomains.Selection.FirstEntryRestriction
import OAI.Analysis.CircleDomains.Modulus.InteriorPhysicalCost

namespace OAI

/-! Truncation at a domain point of an anchor preserves the interior cost
budget, so an omitted dust endpoint is never charged during attachment. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

private theorem exists_domain_time_inside_anchor
    (γ : C(PathTime, X)) {U A : Set X} (hU : IsOpen U)
    (hfront : frontier A ⊆ U) (hstart : γ ⊥ ∈ interior A)
    (hend : γ ⊤ ∉ interior A) :
    ∃t : PathTime, t < ⊤ ∧ γ t ∈ interior A ∩ U := by
  let s := firstExitTime γ (interior A)
  have hspos : ⊥ < s := firstExit_pos γ isOpen_interior hstart hend
  have hsU : γ s ∈ U :=
    hfront (frontier_interior_subset (firstExit_frontier γ isOpen_interior hstart hend))
  have hscl : s ∈ closure (Iio s) := by
    rw [closure_Iio' ⟨⊥, hspos⟩]
    exact (le_rfl : s ≤ s)
  obtain ⟨t, htU, hts⟩ := mem_closure_iff.mp hscl (γ ⁻¹' U)
    (hU.preimage γ.continuous) hsU
  exact ⟨t, hts.trans_le le_top, mem_before_firstExit γ (interior A) hts, htU⟩

variable {Y : Type*} [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem interiorPhysicalTollCost_affine_le
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) {a b : PathTime} (hab : a < b)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞) :
    interiorPhysicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ hab) ≤
      interiorPhysicalTollCost d g m γ := by
  unfold interiorPhysicalTollCost
  rw [physicalCost_affine d.domainEquiv hU d.basePoint γ hab g hg,
    physicalOccupation_integral d.domainEquiv hU d.basePoint γ g hg]
  change _ + timeToll (affineRestrictedPath a b γ.val) (Ioo ⊥ ⊤) m ≤ _
  rw [interiorToll_affine γ.val m hab]
  apply add_le_add (lintegral_mono' Measure.restrict_le_self le_rfl)
  apply timeToll_mono
  intro t ht
  exact ⟨bot_le.trans_lt ht.1, ht.2.trans_le le_top⟩

theorem exists_allowed_suffix_from_anchor
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    {A : Set X} (hfront : frontier A ⊆ d.quotientDomain)
    (hstart : Γ.1.val ⊥ ∈ interior A) (hend : Γ.1.val ⊤ ∉ interior A)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
      ρ.1.val ⊥ ∈ interior A ∩ d.quotientDomain ∧ ρ.1.val ⊤ = Γ.1.val ⊤ ∧
      interiorPhysicalTollCost d g m ρ.1 ≤ interiorPhysicalTollCost d g m Γ.1 := by
  obtain ⟨t, ht, htm⟩ := exists_domain_time_inside_anchor Γ.1.val hU hfront hstart hend
  let ρ := restrictTaggedPhysicalPath d hU Γ ht
  refine ⟨ρ, restrictTaggedPhysicalPath_allowed d hU ν N Γ hΓ hpoint ht, ?_, ?_, ?_⟩
  · exact (restrictTaggedPhysicalPath_zero d hU Γ ht).symm ▸ htm
  · exact restrictTaggedPhysicalPath_one d hU Γ ht
  · exact interiorPhysicalTollCost_affine_le d hU Γ.1 ht g hg m

theorem exists_allowed_prefix_to_anchor
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    {A : Set X} (hfront : frontier A ⊆ d.quotientDomain)
    (hstart : Γ.1.val ⊥ ∉ interior A) (hend : Γ.1.val ⊤ ∈ interior A)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
      ρ.1.val ⊥ = Γ.1.val ⊥ ∧ ρ.1.val ⊤ ∈ interior A ∩ d.quotientDomain ∧
      interiorPhysicalTollCost d g m ρ.1 ≤ interiorPhysicalTollCost d g m Γ.1 := by
  obtain ⟨t, ht, htm⟩ := exists_domain_time_inside_anchor (reversedPath Γ.1.val) hU hfront
    (by simpa only [reversedPath_zero] using hend)
    (by simpa only [reversedPath_one] using hstart)
  have hcut : (⊥ : PathTime) < unitInterval.symm t := by
    have h : unitInterval.symm (1 : PathTime) < unitInterval.symm t :=
      unitInterval.symm_lt_symm.mpr ht
    rw [unitInterval.symm_one] at h
    exact h
  let ρ := restrictTaggedPhysicalPath d hU Γ hcut
  refine ⟨ρ, restrictTaggedPhysicalPath_allowed d hU ν N Γ hΓ hpoint hcut, ?_, ?_, ?_⟩
  · exact restrictTaggedPhysicalPath_zero d hU Γ hcut
  · exact (restrictTaggedPhysicalPath_one d hU Γ hcut).symm ▸ htm
  · exact interiorPhysicalTollCost_affine_le d hU Γ.1 hcut g hg m

end CircleDomainRigidity

end

end OAI
