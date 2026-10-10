import OAI.Analysis.KadisonKastler.ProjectionDimensionStrata

namespace OAI

/-! # The measurable partition by projection rank -/

namespace KadisonKastler

noncomputable section

variable {X : Type*}

theorem frameDimensionStratum_unique (p : X → ℕ → Prop) {x : X} {i j : ℕ}
    (hi : x ∈ frameDimensionStratum p i) (hj : x ∈ frameDimensionStratum p j) : i = j := by
  cases i with
  | zero =>
    cases j with
    | zero => rfl
    | succ n => exact (hj.2 (hi n)).elim
  | succ n =>
    cases j with
    | zero => exact (hi.2 (hj n)).elim
    | succ m =>
      congr 1
      by_contra hnm
      rcases lt_or_gt_of_ne hnm with hlt | hgt
      · exact hi.2 (hj.1 n hlt)
      · exact hj.2 (hi.1 m hgt)

theorem frameDimensionStratum_pairwise (p : X → ℕ → Prop) :
    Pairwise fun i j => Disjoint (frameDimensionStratum p i) (frameDimensionStratum p j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact hij (frameDimensionStratum_unique p hi hj)

theorem iUnion_frameDimensionStratum (p : X → ℕ → Prop) :
    (⋃ n, frameDimensionStratum p n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_frameDimensionStratum p x
  exact Set.mem_iUnion.mpr ⟨n, hn⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (P : X → H →L[ℂ] H) (b : ℕ → H)

theorem projectionRankStratum_pairwise :
    Pairwise fun i j => Disjoint (projectionRankStratum P b i) (projectionRankStratum P b j) :=
  frameDimensionStratum_pairwise _

theorem iUnion_projectionRankStratum : (⋃ n, projectionRankStratum P b n) = Set.univ :=
  iUnion_frameDimensionStratum _

end

end KadisonKastler

end OAI
