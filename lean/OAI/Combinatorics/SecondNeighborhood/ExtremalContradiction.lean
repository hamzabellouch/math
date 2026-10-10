import OAI.Combinatorics.SecondNeighborhood.ExtremalCompatibility
import OAI.Combinatorics.SecondNeighborhood.ExtremalCounting

namespace OAI

namespace SeymourSecondNeighborhood.Extremal

open Pruning

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem complement_gain {r : V → V → Prop} {P Q : Finset (V × V)}
    (h : Admissible r P Q) (hpos : PositiveIndegree r)
    (hgrowth : StrictSubsetGrowth r) :
    P.card + Q.card + 2 * uncoveredCount r P Q <
      (leftCandidate r Q).card + (rightCandidate r P).card := by
  classical
  have hleft := h.strict_leftImage_growth hpos hgrowth
  have hright := h.strict_rightImage_growth hpos hgrowth
  have huncovered := uncoveredCount_add_images h.compatible
  have hR : (leftCandidate r Q).card +
      (rightImage r (rightImage r Q)).card = (Finset.univ : Finset (V × V)).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  have hC : (rightCandidate r P).card +
      (leftImage r (leftImage r P)).card = (Finset.univ : Finset (V × V)).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  omega

theorem no_strictSubsetGrowth_of_pruning {r : V → V → Prop}
    (hr : IsOriented r) (hpos : PositiveIndegree r)
    (hprune : PruningStatement r) : ¬ StrictSubsetGrowth r := by
  classical
  intro hgrowth
  obtain ⟨P, Q, h, hmax⟩ := exists_maximizing_pair r (Admissible r)
    ⟨diagonal, diagonal, diagonal_admissible hr⟩
  obtain ⟨P', Q', hp⟩ := hprune (leftCandidate r Q) (rightCandidate r P)
  have hnext : Admissible r P' Q' := pruning_preserves_diagonal h hp
  have hH : (H r (leftCandidate r Q) (rightCandidate r P)).card ≤
      uncoveredCount r P Q := by
    exact H_candidates_card_le_uncovered r P Q
  have hbetter := objective_lt_of_pruning hp hH (complement_gain h hpos hgrowth)
  exact (not_lt_of_ge (hmax P' Q' hnext)) hbetter

end SeymourSecondNeighborhood.Extremal

end OAI
