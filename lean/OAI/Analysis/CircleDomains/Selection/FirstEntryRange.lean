import OAI.Analysis.CircleDomains.Selection.FirstEntryRestriction

namespace OAI

/-! Cut a path at its first arrival in a closed collar. The retained
prefix avoids the open collar and has no greater full cost. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_first_entry_prefix_with_range
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    {W : Set X} (hW : IsOpen W) (hstart : Γ.1.val ⊥ ∉ closure W)
    (hend : Γ.1.val ⊤ ∈ closure W)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
      ρ.1.val ⊥ = Γ.1.val ⊥ ∧ ρ.1.val ⊤ ∈ frontier W ∧
      range ρ.1.val ⊆ Wᶜ ∧ range ρ.1.val ⊆ range Γ.1.val ∧
      physicalTollCost d g m ρ.1 ≤ physicalTollCost d g m Γ.1 := by
  let V := (closure W)ᶜ
  have hV : IsOpen V := isClosed_closure.isOpen_compl
  have hstop : Γ.1.val ⊤ ∉ V := fun h => h hend
  have hpos := firstExit_pos Γ.1.val hV hstart hstop
  let ρ := restrictTaggedPhysicalPath d hU Γ hpos
  have hlast : ρ.1.val ⊤ = Γ.1.val (firstExitTime Γ.1.val V) :=
    restrictTaggedPhysicalPath_one d hU Γ hpos
  refine ⟨ρ, restrictTaggedPhysicalPath_allowed d hU ν N Γ hΓ hpoint hpos,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact restrictTaggedPhysicalPath_zero d hU Γ hpos
  · rw [hlast]
    have h := firstExit_frontier Γ.1.val hV hstart hstop
    rw [frontier_compl] at h
    exact frontier_closure_subset h
  · rw [restrictTaggedPhysicalPath_range d hU Γ hpos]
    rintro x ⟨t, ht, rfl⟩
    apply closure_minimal (compl_subset_compl.mpr subset_closure) hW.isClosed_compl
    exact firstExit_initial_segment Γ.1.val hV hstart hstop ht.2
  · rw [restrictTaggedPhysicalPath_range d hU Γ hpos]
    exact image_subset_range _ _
  · exact physicalTollCost_affine_le d hU Γ.1 hpos g hg m

end CircleDomainRigidity

end

end OAI
