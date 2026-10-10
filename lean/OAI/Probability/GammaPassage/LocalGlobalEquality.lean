import OAI.Probability.GammaPassage.LocalTrailPassage

namespace OAI

namespace GammaFPP.FiniteLocal
open PlanarFPP

lemma localization_trace_take (p : Vertex) (ds : List Step) (n : ℕ) :
    trace p (ds.take n) = (trace p ds).take n := by
  induction n generalizing p ds with
  | zero => simp [trace]
  | succ n ih =>
      cases ds with
      | nil => simp [trace]
      | cons d ds => simp [trace, ih]

lemma localization_prefix_cost_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) (n : ℕ) :
    pathCost w p (ds.take n) ≤ pathCost w p ds := by
  calc
    _ ≤ pathCost w p (ds.take n) +
        pathCost w (p + displacement (ds.take n)) (ds.drop n) :=
      le_add_of_nonneg_right (pathCost_nonneg hw _ _)
    _ = pathCost w p ds := by
      rw [← pathCost_append, List.take_append_drop]

/-- If no trail of length `R` has cost at most `B`, every trail with cost at most
`B` has fewer than `R` steps. -/
lemma trail_short_of_no_cheap_prefix (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (R : ℕ) (B : ℝ)
    (hno : ¬ ∃ es : List Step, es.length = R ∧
      ((trace p es).map traversalEdge).Nodup ∧ pathCost w p es ≤ B)
    (ds : List Step) (hn : ((trace p ds).map traversalEdge).Nodup)
    (hc : pathCost w p ds ≤ B) : ds.length < R := by
  by_contra hshort
  have hR : R ≤ ds.length := Nat.le_of_not_gt hshort
  apply hno
  refine ⟨ds.take R, ?_, ?_, (localization_prefix_cost_le w hw p ds R).trans hc⟩
  · rw [List.length_take, Nat.min_eq_left hR]
  · rw [localization_trace_take]
    exact hn.sublist ((List.take_sublist R (trace p ds)).map traversalEdge)

/-- Near-optimal paths belong to the finite local family when some endpoint path
has cost below `B` and no trail of length `R` has cost at most `B`. -/
theorem exists_local_near_optimal_of_no_cheap_trail
    (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (p q : Vertex) (R : ℕ) (B : ℝ)
    (hpath : ∃ ds : List Step, p + displacement ds = q ∧ pathCost w p ds < B)
    (hno : ¬ ∃ es : List Step, es.length = R ∧
      ((trace p es).map traversalEdge).Nodup ∧ pathCost w p es ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ds ∈ candidates p q R,
      pathCost w p ds < PlanarFPP.passageTime w p q + ε := by
  obtain ⟨qs, hq, hqcost⟩ := hpath
  have hgap : PlanarFPP.passageTime w p q < B :=
    (PlanarFPP.passageTime_le_cost w hw p q qs hq).trans_lt hqcost
  let δ := min ε ((B - PlanarFPP.passageTime w p q) / 2)
  have hδ : 0 < δ := lt_min hε (by linarith)
  obtain ⟨ds, hend, hn, _hmin, hc⟩ :=
    GammaFPP.LoopErase.exists_near_optimal_simple_path w hw p q δ hδ
  have hδε : δ ≤ ε := min_le_left _ _
  have hδgap : δ ≤ (B - PlanarFPP.passageTime w p q) / 2 := min_le_right _ _
  have hcB : pathCost w p ds ≤ B := by linarith
  have hlen := trail_short_of_no_cheap_prefix w hw p R B hno ds hn hcB
  exact ⟨ds, (mem_candidates p q R ds).mpr ⟨hend, hn, hlen⟩, by linarith⟩

/-- The finite local minimum equals the unrestricted passage time when no trail
of length `R` has cost at most the comparison threshold. -/
theorem passageTime_eq_unrestricted_of_no_cheap_trail
    (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (p q : Vertex) (R : ℕ) (B : ℝ)
    (hR : latticeDistance p q < R)
    (hpath : ∃ ds : List Step, p + displacement ds = q ∧ pathCost w p ds < B)
    (hno : ¬ ∃ es : List Step, es.length = R ∧
      ((trace p es).map traversalEdge).Nodup ∧ pathCost w p es ≤ B) :
    passageTime w p q R = PlanarFPP.passageTime w p q := by
  apply le_antisymm
  · apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨ds, hds, hc⟩ :=
      exists_local_near_optimal_of_no_cheap_trail w hw p q R B hpath hno ε hε
    exact (passageTime_le_candidate w p q R ds hds).trans_lt hc
  · exact unrestricted_passageTime_le w hw p q R hR

/-- Localization at the linear cost threshold `c * R`. -/
theorem passageTime_eq_unrestricted_of_no_cheap_linear_trail
    (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (p q : Vertex) (R : ℕ) (c : ℝ)
    (hR : latticeDistance p q < R)
    (hpath : ∃ ds : List Step, p + displacement ds = q ∧ pathCost w p ds < c * R)
    (hno : ¬ ∃ es : List Step, es.length = R ∧
      ((trace p es).map traversalEdge).Nodup ∧ pathCost w p es ≤ c * R) :
    passageTime w p q R = PlanarFPP.passageTime w p q :=
  passageTime_eq_unrestricted_of_no_cheap_trail w hw p q R (c * R) hR hpath hno

end GammaFPP.FiniteLocal

end OAI
