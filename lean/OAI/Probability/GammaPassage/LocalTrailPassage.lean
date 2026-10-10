import OAI.Probability.GammaPassage.LocalTrailCandidates

namespace OAI

namespace GammaFPP.FiniteLocal
open PlanarFPP

/-- Costs of trails in the finite candidate family. -/
def costs (w : Edge → ℝ) (p q : Vertex) (R : ℕ) : Set ℝ :=
  {c | ∃ ds ∈ candidates p q R, c = pathCost w p ds}

lemma costs_finite (w : Edge → ℝ) (p q : Vertex) (R : ℕ) :
    (costs w p q R).Finite := by
  classical
  apply ((candidates p q R).image (fun ds => pathCost w p ds)).finite_toSet.subset
  rintro c ⟨ds, hds, rfl⟩
  exact Finset.mem_image.mpr ⟨ds, hds, rfl⟩

lemma costs_nonempty (w : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) : (costs w p q R).Nonempty := by
  obtain ⟨ds, hds⟩ := candidates_nonempty p q R hR
  exact ⟨pathCost w p ds, ds, hds, rfl⟩

/-- The infimum of costs among candidate trails. It is a finite minimum whenever
the lattice distance is less than `R`. -/
noncomputable def passageTime (w : Edge → ℝ) (p q : Vertex) (R : ℕ) : ℝ :=
  sInf (costs w p q R)

/-- A nonempty finite candidate family attains its minimum for every real
edge-weight assignment. -/
theorem minimizing_candidate (w : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    ∃ ds ∈ candidates p q R, pathCost w p ds = passageTime w p q R := by
  let C := costs w p q R
  have hC : C.Finite := costs_finite w p q R
  have hne : C.Nonempty := costs_nonempty w p q R hR
  obtain ⟨c, hc, hm⟩ := Set.exists_min_image C id hC hne
  obtain ⟨ds, hds, rfl⟩ := hc
  refine ⟨ds, hds, le_antisymm ?_ ?_⟩
  · exact le_csInf hne (fun c hc => hm c hc)
  · exact csInf_le hC.bddBelow ⟨ds, hds, rfl⟩

lemma passageTime_le_candidate (w : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (ds : List Step) (hds : ds ∈ candidates p q R) :
    passageTime w p q R ≤ pathCost w p ds :=
  csInf_le (costs_finite w p q R).bddBelow ⟨ds, hds, rfl⟩

/-- A minimizing candidate is a trail connecting the endpoints in fewer than
`R` steps. -/
theorem exists_minimizing_trail (w : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    ∃ ds : List Step, p + displacement ds = q ∧
      ((trace p ds).map traversalEdge).Nodup ∧ ds.length < R ∧
      pathCost w p ds = passageTime w p q R := by
  obtain ⟨ds, hds, hc⟩ := minimizing_candidate w p q R hR
  obtain ⟨hend, hn, hl⟩ := (mem_candidates p q R ds).mp hds
  exact ⟨ds, hend, hn, hl, hc⟩

/-- Unrestricted passage time is at most the finite local minimum. -/
theorem unrestricted_passageTime_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) :
    PlanarFPP.passageTime w p q ≤ passageTime w p q R := by
  obtain ⟨ds, hend, _, _, hc⟩ := exists_minimizing_trail w p q R hR
  rw [← hc]
  exact PlanarFPP.passageTime_le_cost w hw p q ds hend

lemma passageTime_nonneg (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) :
    0 ≤ passageTime w p q R :=
  (PlanarFPP.passageTime_nonneg w hw p q).trans
    (unrestricted_passageTime_le w hw p q R hR)

end GammaFPP.FiniteLocal

end OAI
