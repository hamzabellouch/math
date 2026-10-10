import OAI.Analysis.CircleDomains.Topology.CountablePathConcatenation
import OAI.Analysis.CircleDomains.Topology.AffineBoundaryTolls
import OAI.Analysis.CircleDomains.Selection.ConcatenatedResidualPieces

namespace OAI

/-! Exact toll addition for collar pieces. Junctions lie in the physical
 domain, hence carry zero dust toll; the new limiting endpoint is omitted. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
theorem timeToll_eq_of_zero_difference {T : Type*} (γ : T → X) (m : X → ℝ≥0∞)
    {A B : Set T} (hBA : B ⊆ A) (hz : ∀ t ∈ A \ B, m (γ t) = 0) :
    timeToll γ A m = timeToll γ B m := by
  rw [timeToll_eq_indicator, timeToll_eq_indicator]
  apply tsum_congr
  intro t
  by_cases ht : t ∈ B
  · simp only [ht, hBA ht, ite_true]
  · by_cases ha : t ∈ A
    · simp only [ha, ht, ite_true, ite_false, hz t ⟨ha, ht⟩]
    · simp only [ha, ht, ite_false]

theorem timeToll_eq_interior_of_zero_endpoints (γ : C(PathTime, X))
    (m : X → ℝ≥0∞) (hzero : m (γ ⊥) = 0) (hone : m (γ ⊤) = 0) :
    boundaryToll γ m = timeToll γ (Ioo (⊥ : PathTime) ⊤) m := by
  rw [boundaryToll_eq_timeToll]
  apply timeToll_eq_of_zero_difference γ m (subset_univ _)
  intro t ht
  have he : t = ⊥ ∨ t = ⊤ := by
    by_contra h
    push Not at h
    exact ht.2 ⟨bot_lt_iff_ne_bot.mpr h.1, lt_top_iff_ne_top.mpr h.2⟩
  rcases he with rfl | rfl
  · exact hzero
  · exact hone

theorem collarConcatenation_cell_toll (p : X) (γ : ℕ → C(PathTime, X)) hjoin htail
    (m : X → ℝ≥0∞) (n : ℕ) :
    timeToll (collarConcatenation p γ hjoin htail)
        (Ioo (collarTime (n + 1)) (collarTime n)) m =
      timeToll (γ n) (Ioo (⊥ : PathTime) ⊤) m := by
  have he := interiorToll_affine (collarConcatenation p γ hjoin htail) m
    (collarTime_strictAnti (Nat.lt_succ_self n))
  rw [← he]
  apply timeToll_congr_path
  intro t _
  exact collarConcatenation_affine p γ hjoin htail n t

theorem collarConcatenation_interior_toll (p : X) (γ : ℕ → C(PathTime, X)) hjoin htail
    (m : X → ℝ≥0∞) (hzero : ∀ n, m (γ n ⊥) = 0) (hone : ∀ n, m (γ n ⊤) = 0) :
    timeToll (collarConcatenation p γ hjoin htail) (Ioo (⊥ : PathTime) ⊤) m =
      ∑' n, boundaryToll (γ n) m := by
  let η := collarConcatenation p γ hjoin htail
  have hsub : (⋃ n, Ioo (collarTime (n + 1)) (collarTime n)) ⊆ Ioo (⊥ : PathTime) ⊤ := by
    intro t ht
    obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    exact ⟨(collarTime_pos (n + 1)).trans hn.1, hn.2.trans_le le_top⟩
  have hz : ∀ t ∈ Ioo (⊥ : PathTime) ⊤ \ (⋃ n, Ioo (collarTime (n + 1)) (collarTime n)),
      m (η t) = 0 := by
    intro t ht
    obtain ⟨n, hl, hr⟩ := exists_collarTime_cell ht.1.1
    have he : t = collarTime n := by
      by_contra hne
      exact ht.2 (mem_iUnion.mpr ⟨n, hl, hr.lt_of_ne hne⟩)
    have hf := collarConcatenation_affine p γ hjoin htail n ⊤
    rw [affinePathTime_one] at hf
    change m (collarConcatenation p γ hjoin htail t) = 0
    rw [he, hf]
    exact hone n
  rw [timeToll_eq_of_zero_difference η m hsub hz,
    timeToll_iUnion η m _ collarCell_disjoint_interiors]
  apply tsum_congr
  intro n
  exact (collarConcatenation_cell_toll p γ hjoin htail m n).trans
    (timeToll_eq_interior_of_zero_endpoints (γ n) m (hzero n) (hone n)).symm

end CircleDomainRigidity

end

end OAI
