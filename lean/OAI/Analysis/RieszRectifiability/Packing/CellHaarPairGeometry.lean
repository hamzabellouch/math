import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.CellHaarFunctions
import OAI.Analysis.RieszRectifiability.Nets.NestedCellIndicators

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

structure CellHaarPair {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) (I : ℕ) where
  outerOffset : ℕ
  innerOffset : ℕ
  depth_bound : outerOffset + innerOffset ≤ I
  outerCenter : (supportLatticeNets μ R hR (k + outerOffset)).points
  innerCenter : (supportLatticeNets μ R hR (k + outerOffset + innerOffset)).points
  outer_ancestor : supportLatticeAncestor μ R hR k outerOffset outerCenter = z
  inner_ancestor : supportLatticeAncestor μ R hR (k + outerOffset) innerOffset innerCenter = outerCenter

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R} {k I : ℕ}
  {z : (supportLatticeNets μ R hR k).points}

def CellHaarPair.outerCell (P : CellHaarPair μ R hR k z I) : Set (Ambient d) :=
  cleanSupportCell μ R hR (k + P.outerOffset) P.outerCenter

def CellHaarPair.innerCell (P : CellHaarPair μ R hR k z I) : Set (Ambient d) :=
  cleanSupportCell μ R hR (k + P.outerOffset + P.innerOffset) P.innerCenter

def CellHaarPair.test (P : CellHaarPair μ R hR k z I) : Ambient d → ℝ :=
  cellHaar μ P.innerCell P.outerCell

theorem CellHaarPair.outer_subset_parent (P : CellHaarPair μ R hR k z I) :
    P.outerCell ⊆ cleanSupportCell μ R hR k z := by
  have h := cleanSupportCell_nested μ R hR k P.outerOffset P.outerCenter
  rw [P.outer_ancestor] at h
  exact h

theorem CellHaarPair.inner_subset_outer (P : CellHaarPair μ R hR k z I) :
    P.innerCell ⊆ P.outerCell := by
  have h := cleanSupportCell_nested μ R hR (k + P.outerOffset) P.innerOffset P.innerCenter
  rw [P.inner_ancestor] at h
  exact h

theorem CellHaarPair.outer_measurable (P : CellHaarPair μ R hR k z I) : MeasurableSet P.outerCell :=
  cleanSupportCell_measurable μ R hR (k + P.outerOffset) P.outerCenter

theorem CellHaarPair.inner_measurable (P : CellHaarPair μ R hR k z I) : MeasurableSet P.innerCell :=
  cleanSupportCell_measurable μ R hR (k + P.outerOffset + P.innerOffset) P.innerCenter

theorem CellHaarPair.test_zero_outside_parent (P : CellHaarPair μ R hR k z I)
    (x : Ambient d) (hx : x ∉ cleanSupportCell μ R hR k z) : P.test x = 0 :=
  cellHaar_zero_of_notMem μ P.innerCell P.outerCell P.inner_subset_outer x
    (fun h => hx (P.outer_subset_parent h))

theorem CellHaarPair.test_constant_on_finer (P : CellHaarPair μ R hR k z I)
    (l : ℕ) (hl : k + I ≤ l) (w : (supportLatticeNets μ R hR l).points) :
    ∃ c : ℝ, ∀ x ∈ cleanSupportCell μ R hR l w, P.test x = c := by
  have ho : k + P.outerOffset ≤ l := by have h := P.depth_bound; omega
  have hi : k + P.outerOffset + P.innerOffset ≤ l := by have h := P.depth_bound; omega
  obtain ⟨co, hco⟩ := normalizedCellIndicator_const_on_finer μ R hR (k + P.outerOffset) l ho P.outerCenter w
  obtain ⟨ci, hci⟩ := normalizedCellIndicator_const_on_finer μ R hR
    (k + P.outerOffset + P.innerOffset) l hi P.innerCenter w
  refine ⟨Real.sqrt (μ.real P.innerCell) * (ci - co), ?_⟩
  intro x hx
  change Real.sqrt (μ.real P.innerCell) *
    (normalizedSetIndicator μ P.innerCell x - normalizedSetIndicator μ P.outerCell x) = _
  have hix : normalizedSetIndicator μ P.innerCell x = ci := hci x hx
  have hox : normalizedSetIndicator μ P.outerCell x = co := hco x hx
  rw [hix, hox]

end

end RieszRectifiability

end OAI
