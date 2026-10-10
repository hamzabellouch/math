import OAI.Analysis.PureInfiniteness.OneStepPointNormClosure

namespace OAI

/-! A finite-test criterion for membership in point-norm closure. -/

noncomputable section
open Filter Topology Set

namespace WeakPureInfiniteness

variable {B D : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]

omit [NonUnitalCStarAlgebra B] in
theorem mem_closure_of_finite_approximation {S : Set (B → D)} {T : B → D}
    (h : ∀ (F : Finset B) (ε : ℝ), 0 < ε →
      ∃ R ∈ S, ∀ b ∈ F, ‖T b - R b‖ < ε) : T ∈ closure S := by
  classical
  apply mem_closure_iff_nhds.mpr
  intro V hV
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨F, G, hG, hGV⟩ := hV
  have hballs : ∀ b : F, ∃ ε : ℝ, 0 < ε ∧ Metric.ball (T b) ε ⊆ G b := by
    intro b
    exact Metric.mem_nhds_iff.mp (hG b)
  choose ε hε hball using hballs
  let δ := Finset.univ.inf' (by simp : (Finset.univ : Finset (Option F)).Nonempty)
    (fun b : Option F => b.elim 1 ε)
  have hδ : 0 < δ := by
    apply (Finset.lt_inf'_iff _).mpr
    intro b _
    cases b with
    | none => exact zero_lt_one
    | some b => exact hε b
  obtain ⟨R, hRS, hR⟩ := h F δ hδ
  refine ⟨R, hGV ?_, hRS⟩
  intro b hb
  apply hball ⟨b, hb⟩
  change dist (R b) (T b) < ε ⟨b, hb⟩
  rw [dist_eq_norm, norm_sub_rev]
  have hδε : δ ≤ ε ⟨b, hb⟩ := Finset.inf'_le _ (Finset.mem_univ (some (⟨b, hb⟩ : F)))
  exact (hR b hb).trans_le hδε

end WeakPureInfiniteness

end

end OAI
