import OAI.Analysis.CircleDomains.Probability.PhysicalOccupationCode

namespace OAI

/-! A simple arc has no occupation atom at its starting point. Thus a
terminal arc whose other points lie inside a collar is paid for by the
original occupation restricted to that collar. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem simple_arc_physical_occupation (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (α : FinitePhysicalPath e y₀) (hi : Injective α.val) :
    dyadicPhysicalOccupation e y₀ α = (μH[1] : Measure Y).restrict
      ((physicalValue e y₀ ∘ α.val) '' (α.val ⁻¹' U)) :=
  le_antisymm (simple_arc_physical_occupation_le e hU y₀ α hi)
    (physical_image_hausdorff_le_occupation e hU y₀ α)

theorem simple_arc_physical_support (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (α : FinitePhysicalPath e y₀) (hi : Injective α.val)
    {W : Set Y} (hW : MeasurableSet W) (y : Y)
    (hout : ∀ t, α.val t ∈ U → physicalValue e y₀ (α.val t) ∉ W →
      physicalValue e y₀ (α.val t) = y) :
    (dyadicPhysicalOccupation e y₀ α).restrict W = dyadicPhysicalOccupation e y₀ α := by
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  change dyadicPhysicalOccupation e y₀ α Wᶜ = 0
  rw [simple_arc_physical_occupation e hU y₀ α hi, Measure.restrict_apply hW.compl]
  let : NullSingletonClass (μH[1] : Measure Y) :=
    Measure.nullSingletonClass_hausdorff Y (by norm_num)
  apply measure_mono_null (t := {y})
  · rintro z ⟨hz, t, ht, rfl⟩
    exact hout t ht hz
  · exact measure_singleton y

theorem simple_subarc_physical_localized_le (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ α : FinitePhysicalPath e y₀)
    (hi : Injective α.val) (hs : range α.val ⊆ range γ.val)
    {W : Set Y} (hW : MeasurableSet W) (y : Y)
    (hout : ∀ t, α.val t ∈ U → physicalValue e y₀ (α.val t) ∉ W →
      physicalValue e y₀ (α.val t) = y) :
    dyadicPhysicalOccupation e y₀ α ≤ (dyadicPhysicalOccupation e y₀ γ).restrict W := by
  rw [← simple_arc_physical_support e hU y₀ α hi hW y hout]
  exact Measure.restrict_mono_measure (simple_subarc_physical_occupation_le e hU y₀ γ α hi hs) W

variable [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace X] [BorelSpace X] in
lemma physicalValue_projects (e : G ≃ₜ U) (y₀ : Y) (π : Y → X)
    (hπ : ∀ y : G, π y.val = (e y).val) {x : X} (hx : x ∈ U) :
    π (physicalValue e y₀ x) = x := by
  simp only [physicalValue, dite_eq_left hx]
  rw [hπ]
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

omit [BorelSpace X] in
theorem simple_subarc_physical_collar_le (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (π : Y → X) (hπm : Measurable π)
    (hπ : ∀ y : G, π y.val = (e y).val)
    (γ α : FinitePhysicalPath e y₀)
    (hi : Injective α.val) (hs : range α.val ⊆ range γ.val)
    (V : Set X) (hV : MeasurableSet V)
    (hout : ∀ t, α.val t ∉ V → α.val t = α.val ⊥) :
    dyadicPhysicalOccupation e y₀ α ≤ (dyadicPhysicalOccupation e y₀ γ).restrict (π ⁻¹' V) := by
  apply simple_subarc_physical_localized_le e hU y₀ γ α hi hs (hπm hV)
    (physicalValue e y₀ (α.val ⊥))
  intro t ht hn
  apply congrArg (physicalValue e y₀)
  apply hout t
  simpa only [mem_preimage, physicalValue_projects e y₀ π hπ ht] using hn

end CircleDomainRigidity

end

end OAI
