import OAI.Computability.BinPacking.Inventory.EdgeLongConsumption
import OAI.Computability.BinPacking.Packing.ExtractedCover

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinPackingGap

private def leftIncidencePosition (G : GraphInput) (R : ℕ) (edge : G.Edge) (j : Fin R) :
    G.IncidencePosition R (G.left edge) :=
  (⟨(edge, 0), G.endpoint_zero edge⟩, j)

private def rightIncidencePosition (G : GraphInput) (R : ℕ) (edge : G.Edge) (j : Fin R) :
    G.IncidencePosition R (G.right edge) :=
  (⟨(edge, 1), G.endpoint_one edge⟩, j)

theorem extractedCover_isCover (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ)
    (hk : k ≤ G.n) {b : ℕ} (p : Packing (reductionInstance c ρ G k) b)
    (hb : b ≤ reductionBinBound c ρ G k + c) :
    G.IsCover (extractedCover c ρ G k p) := by
  classical
  let D := reductionInventory c ρ G k
  let Sleft : G.Edge → Finset (Fin D.R) := fun edge =>
    PackingCounts.goodRepetitions p D.itemEquiv (G.left edge) edge
  let Sright : G.Edge → Finset (Fin D.R) := fun edge =>
    PackingCounts.goodRepetitions p D.itemEquiv (G.right edge) edge
  let Lleft : G.Edge → Fin D.R → ℕ := fun edge j =>
    (D.edgeLongTuplesAt p edge (0, j)).card
  let Lright : G.Edge → Fin D.R → ℕ := fun edge j =>
    (D.edgeLongTuplesAt p edge (1, j)).card
  have hL : 1 ≤ D.L := Nat.succ_le_of_lt (reductionInventory_height_pos c ρ G k)
  apply thresholdCover_isCover G (PackingCounts.xplus p D.itemEquiv)
    Sleft Sright Lleft Lright (depthDemand_one_le c ρ) (depthDemand_ge_72 c ρ)
    (reductionInventory_R c ρ G k)
  · intro edge
    exact PackingCounts.goodRepetitions_card_ge_real p D.itemEquiv hL (G.left edge) edge
  · intro edge
    exact PackingCounts.goodRepetitions_card_ge_real p D.itemEquiv hL (G.right edge) edge
  · intro edge j hj
    have hj' : (edge, j) ∉ PackingCounts.excludedAt p D.itemEquiv (G.left edge) :=
      (mem_nonexcludedRepetitions _ _).mp hj
    exact D.long_matches_at_nonexcluded (reductionInventory_plus_height c ρ G k)
      (reductionInventory_minus_height c ρ G k) hL hk p hb (G.left edge)
      (leftIncidencePosition G D.R edge j) hj'
  · intro edge j hj
    have hj' : (edge, j) ∉ PackingCounts.excludedAt p D.itemEquiv (G.right edge) :=
      (mem_nonexcludedRepetitions _ _).mp hj
    exact D.long_matches_at_nonexcluded (reductionInventory_plus_height c ρ G k)
      (reductionInventory_minus_height c ρ G k) hL hk p hb (G.right edge)
      (rightIncidencePosition G D.R edge j) hj'
  · intro edge
    have hcap := D.edge_long_matches_capacity hk p hb edge Finset.univ
    have htwo : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    change (∑ j : Fin D.R, Lleft edge j) + (∑ j : Fin D.R, Lright edge j) ≤
      D.d * D.R + 3 * D.graph.n * lossAllowance c
    simpa [htwo, Lleft, Lright] using hcap

theorem packing_extracts_cover (c : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (G : GraphInput) (k : ℕ) (hk : k ≤ G.n) {b : ℕ}
    (p : Packing (reductionInstance c ρ G k) b)
    (hb : b ≤ reductionBinBound c ρ G k + c) :
    ∃ C : Finset G.Vertex, G.IsCover C ∧ (C.card : ℝ) ≤ (k : ℝ) + ρ * G.n :=
  ⟨extractedCover c ρ G k p, extractedCover_isCover c ρ G k hk p hb,
    extractedCover_card_le c ρ hρ G k hk p hb⟩

end BinPackingGap

end

namespace BinPackingGap

theorem completeFourGraph_reduction_no_packing (c : ℕ) :
    ¬ HasPacking (reductionInstance c (1 / 8) completeFourGraph 2)
      (reductionBinBound c (1 / 8) completeFourGraph 2 + c) := by
  rintro ⟨p⟩
  exact completeFourGraph_no_small_cover
    (packing_extracts_cover c (1 / 8) (by norm_num) completeFourGraph 2
      (by decide) p le_rfl)

theorem completeFourGraph_reduction_opt_gap (c : ℕ) :
    reductionBinBound c (1 / 8) completeFourGraph 2 + c <
      opt (reductionInstance c (1 / 8) completeFourGraph 2) :=
  (not_hasPacking_iff_lt_opt _ _).mp (completeFourGraph_reduction_no_packing c)

end BinPackingGap

end OAI
