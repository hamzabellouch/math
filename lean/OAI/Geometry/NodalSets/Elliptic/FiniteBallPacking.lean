import Mathlib.MeasureTheory.Covering.Vitali

namespace OAI

namespace Yau
open Set Metric
noncomputable section

lemma finite_fivefold_packing {E : Type*} [PseudoMetricSpace E]
    {Q : Set E} (hQ : IsCompact Q) (r : E → ℝ) (hr : ∀ x ∈ Q, 0 < r x) :
    ∃ t : Finset E, (↑t : Set E) ⊆ Q ∧
      (↑t : Set E).PairwiseDisjoint (fun x ↦ closedBall x (r x)) ∧
      Q ⊆ ⋃ x ∈ t, closedBall x (5*r x) := by
  classical
  obtain ⟨v,hvQ,hvfin,hcover⟩ := hQ.elim_finite_subcover_image
    (fun x (_ : x ∈ Q) ↦ isOpen_ball (x := x) (ε := r x))
    (show Q ⊆ ⋃ x ∈ Q, ball x (r x) from fun x hx ↦
      mem_iUnion₂.mpr ⟨x,hx,mem_ball_self (hr x hx)⟩)
  obtain ⟨R,hR⟩ := (hvfin.image r).bddAbove
  obtain ⟨u,huv,hdis,hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall v id r R
      (fun x hx ↦ hR (mem_image_of_mem r hx)) 5 (by norm_num)
  have hufin := hvfin.subset huv
  refine ⟨hufin.toFinset,by simpa using huv.trans hvQ,by simpa using hdis,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hcover hx)
  obtain ⟨z,hz,hzcover⟩ := hcov y hy
  exact mem_iUnion₂.mpr ⟨z,hufin.mem_toFinset.mpr hz,hzcover (ball_subset_closedBall hxy)⟩

end
end Yau

end OAI
