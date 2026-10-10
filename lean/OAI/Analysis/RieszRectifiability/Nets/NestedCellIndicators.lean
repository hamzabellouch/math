import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.FiniteSupportRefinements
import OAI.Analysis.RieszRectifiability.Foundations.NormalizedSetIndicators

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem cleanSupportCell_nested_or_disjoint {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k l : ℕ) (hkl : k ≤ l)
    (z : (supportLatticeNets μ R hR k).points) (w : (supportLatticeNets μ R hR l).points) :
    cleanSupportCell μ R hR l w ⊆ cleanSupportCell μ R hR k z ∨
      Disjoint (cleanSupportCell μ R hR l w) (cleanSupportCell μ R hR k z) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkl
  by_cases h : supportLatticeAncestor μ R hR k t w = z
  · left
    simpa only [h] using! cleanSupportCell_nested μ R hR k t w
  · right
    exact (cleanSupportCell_disjoint μ R hR k _ z h).mono_left
      (cleanSupportCell_nested μ R hR k t w)

theorem normalizedSetIndicator_const_of_nested_or_disjoint {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A B : Set X) (h : B ⊆ A ∨ Disjoint B A) :
    ∃ c : ℝ, ∀ x ∈ B, normalizedSetIndicator μ A x = c := by
  rcases h with h | h
  · exact ⟨(μ.real A)⁻¹, fun x hx => normalizedSetIndicator_of_mem μ A x (h hx)⟩
  · exact ⟨0, fun x hx => normalizedSetIndicator_of_notMem μ A x
      (fun hy => Set.disjoint_left.mp h hx hy)⟩

theorem normalizedCellIndicator_const_on_finer {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k l : ℕ) (hkl : k ≤ l)
    (z : (supportLatticeNets μ R hR k).points) (w : (supportLatticeNets μ R hR l).points) :
    ∃ c : ℝ, ∀ x ∈ cleanSupportCell μ R hR l w,
      normalizedSetIndicator μ (cleanSupportCell μ R hR k z) x = c :=
  normalizedSetIndicator_const_of_nested_or_disjoint μ _ _
    (cleanSupportCell_nested_or_disjoint μ R hR k l hkl z w)

end

end RieszRectifiability

end OAI
