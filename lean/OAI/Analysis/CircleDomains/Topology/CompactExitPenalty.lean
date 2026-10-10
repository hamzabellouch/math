import OAI.Analysis.CircleDomains.Selection.PhysicalExitPenalty
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-! Compact separation supplies the positive physical width and hence an
actual bounded indicator penalty. No path-cost lower bound is assumed. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_compact_exit_penalty
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (π : Y → X) (hπ : Continuous π)
    (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (O : Set X) (hO : IsOpen O) (hOU : closure O ⊆ d.quotientDomain)
    (A : Set Y) (hA : IsCompact A) (hAO : A ⊆ π ⁻¹' O) :
    ∃h : Y → ℝ≥0∞, ∃C : ℝ≥0∞,
      Measurable h ∧ C ≠ ∞ ∧ (∀y, h y ≤ C) ∧ (∀y ∉ π ⁻¹' O, h y = 0) ∧
      ∀γ : FinitePhysicalPath d.domainEquiv d.basePoint,
        ∀hs : γ.val ⊥ ∈ O, γ.val ⊤ ∉ O →
        (d.domainEquiv.symm ⟨γ.val ⊥, hOU (subset_closure hs)⟩).val ∈ A →
        ∀m : X → ℝ≥0∞, 1 ≤ physicalTollCost d h m γ := by
  have hd : Disjoint A (π ⁻¹' O)ᶜ := Set.disjoint_left.mpr fun _ ha hn => hn (hAO ha)
  obtain ⟨δ, hδ, hsep⟩ := Metric.exists_pos_forall_lt_edist hA (hO.preimage hπ).isClosed_compl hd
  have hδ0 : (δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hδ.ne'
  let C : ℝ≥0∞ := (δ : ℝ≥0∞)⁻¹
  let h : Y → ℝ≥0∞ := (π ⁻¹' O).indicator (fun _ => C)
  refine ⟨h, C, measurable_const.indicator (hO.preimage hπ).measurableSet,
    ENNReal.inv_ne_top.mpr hδ0, ?_, ?_, ?_⟩
  · intro y
    change (π ⁻¹' O).indicator (fun _ => C) y ≤ C
    by_cases hy : y ∈ π ⁻¹' O
    · exact le_of_eq (Set.indicator_of_mem hy _)
    · rw [Set.indicator_of_notMem hy]
      exact bot_le
  · intro y hy
    exact Set.indicator_of_notMem hy _
  · intro γ hs ht ha m
    exact first_exit_indicator_cost_lower_bound d hU π hπ he O hO hOU A hδ0 (by simp)
      (fun a ha b hb => (hsep a ha b hb).le) γ hs ht ha m

end CircleDomainRigidity

end

end OAI
