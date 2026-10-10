import OAI.Combinatorics.BalancedRyser.Incidence.ProjectiveIncidence

namespace OAI

section

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def skewThroughExcept (B : Finset (ProjectivePoint F)) (ell : ProjectiveLine F)
    (P : ProjectivePoint F) : Finset (ProjectiveLine F) :=
  ((projectivePencil P).erase ell).filter (fun l => l ∈ skewProjective B)

@[simp] theorem mem_skewThroughExcept (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) (P : ProjectivePoint F) (l : ProjectiveLine F) :
    l ∈ skewThroughExcept B ell P ↔
      l ≠ ell ∧ ProjectiveIncident P l ∧ l ∈ skewProjective B := by
  simp [skewThroughExcept, and_assoc]

theorem card_nonSkew_pencil_erase_le (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) (P : ProjectivePoint F)
    (hP : ProjectiveIncident P ell) (hPB : P ∉ B) :
    (((projectivePencil P).erase ell).filter (fun l => l ∉ skewProjective B)).card ≤
      (B \ projectiveLinePoints ell).card := by
  classical
  apply Finset.card_le_card_of_surjOn (projectiveJoin P)
  intro l hl
  change l ∈ ((projectivePencil P).erase ell).filter (fun l => l ∉ skewProjective B) at hl
  simp only [Finset.mem_filter, Finset.mem_erase, mem_projectivePencil] at hl
  obtain ⟨⟨hlne, hPl⟩, hbad⟩ := hl
  have hex : ∃ Q ∈ B, ProjectiveIncident Q l := by
    simpa only [skewProjective, Finset.mem_filter, Finset.mem_univ, true_and,
      not_forall, not_not, exists_prop] using hbad
  obtain ⟨Q, hQB, hQl⟩ := hex
  have hPQ : P ≠ Q := fun h => hPB (h.symm ▸ hQB)
  have hQell : ¬ ProjectiveIncident Q ell := by
    intro h
    exact hlne (eq_of_two_common_projective_points P Q hPQ l ell hPl hQl hP h)
  refine ⟨Q, ?_, ?_⟩
  · exact Finset.mem_sdiff.mpr ⟨hQB, by simpa using hQell⟩
  · exact (eq_projectiveJoin_of_incident P Q hPQ l hPl hQl).symm

theorem card_skewThroughExcept_ge (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) (P : ProjectivePoint F)
    (hP : ProjectiveIncident P ell) (hPB : P ∉ B) :
    Fintype.card F - (B \ projectiveLinePoints ell).card ≤
      (skewThroughExcept B ell P).card := by
  have hcount : ((projectivePencil P).erase ell).card = Fintype.card F := by
    rw [Finset.card_erase_of_mem ((mem_projectivePencil P ell).mpr hP), card_projectivePencil]
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (projectivePencil P).erase ell) (p := fun l => l ∈ skewProjective B)
  have hblocked := card_nonSkew_pencil_erase_le B ell P hP hPB
  change (((projectivePencil P).erase ell).filter (fun l => l ∈ skewProjective B)).card +
    (((projectivePencil P).erase ell).filter (fun l => l ∉ skewProjective B)).card =
    ((projectivePencil P).erase ell).card at hsplit
  unfold skewThroughExcept
  omega

theorem skewThroughExcept_disjoint (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) {P Q : ProjectivePoint F} (hPQ : P ≠ Q)
    (hP : ProjectiveIncident P ell) (hQ : ProjectiveIncident Q ell) :
    Disjoint (skewThroughExcept B ell P) (skewThroughExcept B ell Q) := by
  apply Finset.disjoint_left.mpr
  intro l hlP hlQ
  obtain ⟨hlne, hPl, _⟩ := (mem_skewThroughExcept B ell P l).mp hlP
  obtain ⟨_, hQl, _⟩ := (mem_skewThroughExcept B ell Q l).mp hlQ
  exact hlne (eq_of_two_common_projective_points P Q hPQ l ell hPl hQl hP hQ)

theorem missing_mul_order_sub_offLine_le_skew (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) :
    (projectiveLinePoints ell \ B).card *
      (Fintype.card F - (B \ projectiveLinePoints ell).card) ≤
      (skewProjective B).card := by
  classical
  let S := projectiveLinePoints ell \ B
  have hdis : (↑S : Set (ProjectivePoint F)).PairwiseDisjoint (skewThroughExcept B ell) := by
    intro P hP Q hQ hPQ
    exact skewThroughExcept_disjoint B ell hPQ
      ((mem_projectiveLinePoints ell P).mp (Finset.mem_sdiff.mp hP).1)
      ((mem_projectiveLinePoints ell Q).mp (Finset.mem_sdiff.mp hQ).1)
  have hsub : S.biUnion (skewThroughExcept B ell) ⊆ skewProjective B := by
    intro l hl
    obtain ⟨P, _, hPl⟩ := Finset.mem_biUnion.mp hl
    exact ((mem_skewThroughExcept B ell P l).mp hPl).2.2
  calc
    S.card * (Fintype.card F - (B \ projectiveLinePoints ell).card) =
        ∑ _P ∈ S, (Fintype.card F - (B \ projectiveLinePoints ell).card) := by simp
    _ ≤ ∑ P ∈ S, (skewThroughExcept B ell P).card := by
      apply Finset.sum_le_sum
      intro P hP
      exact card_skewThroughExcept_ge B ell P
        ((mem_projectiveLinePoints ell P).mp (Finset.mem_sdiff.mp hP).1)
        (Finset.mem_sdiff.mp hP).2
    _ = (S.biUnion (skewThroughExcept B ell)).card := (Finset.card_biUnion hdis).symm
    _ ≤ (skewProjective B).card := Finset.card_le_card hsub

end Balanced

end

section

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [DecidableEq F] in

theorem card_projectiveLines :
    Fintype.card (ProjectiveLine F) = Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp only [ProjectiveLine, Line, Direction, Fintype.card_option, Fintype.card_prod]
  ring

theorem skewProjective_eq_compl_pencils (B : Finset (ProjectivePoint F)) :
    skewProjective B = Finset.univ \ B.biUnion projectivePencil := by
  ext l
  simp [skewProjective, projectivePencil]

theorem projective_order_le_skew_add_pencils (B : Finset (ProjectivePoint F)) :
    Fintype.card F ^ 2 + Fintype.card F + 1 ≤
      (skewProjective B).card + B.card * (Fintype.card F + 1) := by
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (B.biUnion projectivePencil))
  rw [← skewProjective_eq_compl_pencils, Finset.card_univ, card_projectiveLines] at hsplit
  have hbound : (B.biUnion projectivePencil).card ≤ B.card * (Fintype.card F + 1) := by
    calc
      _ ≤ ∑ P ∈ B, (projectivePencil P).card := Finset.card_biUnion_le
      _ = _ := by simp [card_projectivePencil]
  omega

theorem card_skewProjective_pos_of_card_le_order (B : Finset (ProjectivePoint F))
    (hB : B.card ≤ Fintype.card F) : 0 < (skewProjective B).card := by
  have h := projective_order_le_skew_add_pencils B
  have hb := Nat.mul_le_mul_right (Fintype.card F + 1) hB
  nlinarith

theorem exists_skewProjective_of_card_le_order (B : Finset (ProjectivePoint F))
    (hB : B.card ≤ Fintype.card F) :
    ∃ l : ProjectiveLine F, ∀ P ∈ B, ¬ ProjectiveIncident P l := by
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (card_skewProjective_pos_of_card_le_order B hB)
  exact ⟨l, (Finset.mem_filter.mp hl).2⟩

theorem card_skew_dualPointSet_pos (C : Finset (Line F))
    (hC : C.card ≤ Fintype.card F) :
    0 < (skewProjective (dualPointSet C)).card := by
  apply card_skewProjective_pos_of_card_le_order
  simpa only [card_dualPointSet] using hC

end Balanced

end

end OAI
