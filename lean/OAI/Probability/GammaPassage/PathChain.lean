import OAI.Probability.GammaPassage.OriginEscape

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology

theorem pathIn_append (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (hd : PathIn p ds S) (he : PathIn (p+displacement ds) es S) :
    PathIn p (ds++es) S := by
  intro i hi
  by_cases hid : i ≤ ds.length
  · simpa only [List.take_append, Nat.sub_eq_zero_of_le hid, List.take_zero,
      List.append_nil] using hd i hid
  · have hle : ds.length ≤ i := by omega
    have hie : i-ds.length ≤ es.length := by simp only [List.length_append] at hi; omega
    have hh := he (i-ds.length) hie
    simpa only [List.take_append, List.take_of_length_le hle, displacement_append,
      add_assoc] using hh

/-- Concatenating a finite list of connections preserves vertex localization and adds traversal costs. -/
theorem exists_path_chain (w : Edge → ℝ) (p : ℕ → Vertex) (S : Set Vertex)
    (a : ℕ → ℝ) (n : ℕ) (hp : p 0 ∈ S)
    (h : ∀ i < n, ∃ ds, p i+displacement ds=p (i+1) ∧
      pathCost w (p i) ds ≤ a i ∧ PathIn (p i) ds S) :
    ∃ ds, p 0+displacement ds=p n ∧
      pathCost w (p 0) ds ≤ ∑ i ∈ range n, a i ∧ PathIn (p 0) ds S := by
  induction n with
  | zero =>
    refine ⟨[],by simp,by simp [pathCost],?_⟩
    intro i hi
    simpa using hp
  | succ n ih =>
    obtain ⟨ds,hd,hcostd,hind⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    obtain ⟨es,he,hcoste,hine⟩ := h n (Nat.lt_succ_self n)
    refine ⟨ds++es,?_,?_,?_⟩
    · rw [displacement_append, ← add_assoc, hd]
      exact he
    · rw [pathCost_append, hd, sum_range_succ]
      exact add_le_add hcostd hcoste
    · apply pathIn_append _ _ _ _ hind
      simpa only [hd] using hine

end GammaFPP.IntervalTravelBridge

end OAI
