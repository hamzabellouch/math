import Mathlib.Combinatorics.Enumerative.DoubleCounting
import OAI.Combinatorics.BalancedRyser.Incidence.AffineDoubleCount
import OAI.Combinatorics.BalancedRyser.Incidence.AffineMomentAlgebraLemmas
import OAI.Combinatorics.BalancedRyser.Incidence.StabilitySkewCountLemmas

namespace OAI

namespace Balanced.StabilityTangents

open scoped BigOperators
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def tangents (B : Finset (ProjectivePoint F)) : Finset (ProjectiveLine F) :=
  Finset.univ.filter fun l => (B.filter (fun P => ProjectiveIncident P l)).card = 1

@[simp] theorem mem_tangents (B : Finset (ProjectivePoint F)) (l : ProjectiveLine F) :
    l ∈ tangents B ↔ (B.filter (fun P => ProjectiveIncident P l)).card = 1 := by
  simp [tangents]

theorem intersection_card_zero_iff (B : Finset (ProjectivePoint F)) (l : ProjectiveLine F) :
    (B.filter (fun P => ProjectiveIncident P l)).card = 0 ↔ l ∈ skewProjective B := by
  simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff, skewProjective]

theorem sum_intersections_le_card (B : Finset (ProjectivePoint F))
    (P : ProjectivePoint F) (hPB : P ∉ B) (S : Finset (ProjectiveLine F))
    (hS : S ⊆ projectivePencil P) :
    ∑ l ∈ S, (B.filter (fun Q => ProjectiveIncident Q l)).card ≤ B.card := by
  have hswap : (∑ l ∈ S, (B.filter (fun Q => ProjectiveIncident Q l)).card) =
      ∑ Q ∈ B, (S.filter (ProjectiveIncident Q)).card := by
    simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := ProjectiveIncident) (s := B) (t := S)).symm
  rw [hswap]
  calc
    ∑ Q ∈ B, (S.filter (ProjectiveIncident Q)).card ≤ ∑ _Q ∈ B, 1 := by
      apply Finset.sum_le_sum
      intro Q hQB
      apply Finset.card_le_one.mpr
      intro l hl m hm
      exact eq_of_two_common_projective_points P Q (fun h => hPB (h.symm ▸ hQB)) l m
        ((mem_projectivePencil P l).mp (hS (Finset.mem_filter.mp hl).1))
        (Finset.mem_filter.mp hl).2
        ((mem_projectivePencil P m).mp (hS (Finset.mem_filter.mp hm).1))
        (Finset.mem_filter.mp hm).2
    _ = B.card := by simp

theorem twice_card_le_intersections_and_small (B : Finset (ProjectivePoint F))
    (S : Finset (ProjectiveLine F)) :
    2 * S.card ≤ (∑ l ∈ S, (B.filter (fun P => ProjectiveIncident P l)).card) +
      2 * (S.filter (fun l => l ∈ skewProjective B)).card +
      (S.filter (fun l => l ∈ tangents B)).card := by
  let n := fun l => (B.filter (fun P => ProjectiveIncident P l)).card
  have hpoint (l : ProjectiveLine F) :
      2 ≤ n l + (if n l = 0 then 2 else 0) + (if n l = 1 then 1 else 0) := by
    split_ifs <;> omega
  have hs := Finset.sum_le_sum (s := S) (fun l _ => hpoint l)
  have hz : (∑ l ∈ S, if n l = 0 then 2 else 0) =
      2 * (S.filter (fun l => l ∈ skewProjective B)).card := by
    simp only [n, intersection_card_zero_iff]
    rw [← Finset.sum_filter]
    simp [Nat.mul_comm]
  have ht : (∑ l ∈ S, if n l = 1 then 1 else 0) =
      (S.filter (fun l => l ∈ tangents B)).card := by
    simp only [n, ← mem_tangents]
    rw [← Finset.sum_filter]
    simp
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hs
  rw [hz, ht] at hs
  simpa only [n, Nat.mul_comm S.card 2] using hs

theorem sum_pencil_erase_filter_le (ell : ProjectiveLine F) (T : Finset (ProjectiveLine F)) :
    (∑ P ∈ projectiveLinePoints ell,
      (((projectivePencil P).erase ell).filter (fun l => l ∈ T)).card) ≤ T.card := by
  let fibers := fun P => ((projectivePencil P).erase ell).filter (fun l => l ∈ T)
  have hd : (↑(projectiveLinePoints ell) : Set (ProjectivePoint F)).PairwiseDisjoint fibers := by
    intro P hP Q hQ hPQ
    apply Finset.disjoint_left.mpr
    intro l hlP hlQ
    obtain ⟨hlne, hPl⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hlP).1
    obtain ⟨_, hQl⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hlQ).1
    exact hlne (eq_of_two_common_projective_points P Q hPQ l ell
      ((mem_projectivePencil P l).mp hPl) ((mem_projectivePencil Q l).mp hQl)
      ((mem_projectiveLinePoints ell P).mp hP) ((mem_projectiveLinePoints ell Q).mp hQ))
  have hsub : (projectiveLinePoints ell).biUnion fibers ⊆ T := by
    intro l hl
    obtain ⟨P, _, hPl⟩ := Finset.mem_biUnion.mp hl
    exact (Finset.mem_filter.mp hPl).2
  rw [← Finset.card_biUnion hd]
  exact Finset.card_le_card hsub

theorem total_tangents_bound (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) (hell : ell ∈ skewProjective B) :
    2 * Fintype.card F * (Fintype.card F + 1) ≤
      B.card * (Fintype.card F + 1) + 2 * (skewProjective B).card + (tangents B).card := by
  have hlocal (P : ProjectivePoint F) (hP : P ∈ projectiveLinePoints ell) :
      2 * Fintype.card F ≤ B.card +
        2 * (((projectivePencil P).erase ell).filter (fun l => l ∈ skewProjective B)).card +
        (((projectivePencil P).erase ell).filter (fun l => l ∈ tangents B)).card := by
    have hPB : P ∉ B := by
      intro hPB
      exact (Finset.mem_filter.mp hell).2 P hPB ((mem_projectiveLinePoints ell P).mp hP)
    have hc : ((projectivePencil P).erase ell).card = Fintype.card F := by
      rw [Finset.card_erase_of_mem ((mem_projectivePencil P ell).mpr
        ((mem_projectiveLinePoints ell P).mp hP)), card_projectivePencil]
      omega
    have hs := sum_intersections_le_card B P hPB ((projectivePencil P).erase ell)
      (Finset.erase_subset _ _)
    have ht := twice_card_le_intersections_and_small B ((projectivePencil P).erase ell)
    rw [hc] at ht
    omega
  have hs := Finset.sum_le_sum (s := projectiveLinePoints ell) hlocal
  have hzero := sum_pencil_erase_filter_le ell (skewProjective B)
  have hone := sum_pencil_erase_filter_le ell (tangents B)
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    ← Finset.mul_sum, card_projectiveLinePoints] at hs
  nlinarith

theorem sum_tangencies (B : Finset (ProjectivePoint F)) :
    (∑ P ∈ B, ((tangents B).filter (ProjectiveIncident P)).card) = (tangents B).card := by
  calc
    (∑ P ∈ B, ((tangents B).filter (ProjectiveIncident P)).card) =
        ∑ l ∈ tangents B, (B.filter (fun P => ProjectiveIncident P l)).card := by
      simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
        (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (r := ProjectiveIncident) (s := B) (t := tangents B))
    _ = ∑ _l ∈ tangents B, 1 := by
      apply Finset.sum_congr rfl
      intro l hl
      exact (mem_tangents B l).mp hl
    _ = (tangents B).card := by simp

theorem exists_tangent_rich_point (B : Finset (ProjectivePoint F))
    (hB : B.Nonempty) (ell : ProjectiveLine F) (hell : ell ∈ skewProjective B)
    (hsize : (B.card : ℝ) ≤ (3 / 2 : ℝ) * ((Fintype.card F : ℝ) + 1)) :
    ∃ P ∈ B, (2 / 3 : ℝ) * (2 * (Fintype.card F : ℝ) - B.card -
      2 * ((skewProjective B).card : ℝ) / ((Fintype.card F : ℝ) + 1)) ≤
      (((tangents B).filter (ProjectiveIncident P)).card : ℝ) := by
  let a : ℝ := (2 / 3 : ℝ) * (2 * (Fintype.card F : ℝ) - B.card -
      2 * ((skewProjective B).card : ℝ) / ((Fintype.card F : ℝ) + 1))
  by_cases ha : a ≤ 0
  · obtain ⟨P, hP⟩ := hB
    exact ⟨P, hP, ha.trans (Nat.cast_nonneg _)⟩
  have hapos : 0 ≤ a := le_of_lt (lt_of_not_ge ha)
  have htotal : 2 * (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      (B.card : ℝ) * ((Fintype.card F : ℝ) + 1) +
        2 * ((skewProjective B).card : ℝ) + ((tangents B).card : ℝ) := by
    exact_mod_cast total_tangents_bound B ell hell
  have hq : (Fintype.card F : ℝ) + 1 ≠ 0 := by positivity
  have haeq : (3 / 2 : ℝ) * ((Fintype.card F : ℝ) + 1) * a =
      2 * (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1) -
        (B.card : ℝ) * ((Fintype.card F : ℝ) + 1) -
        2 * ((skewProjective B).card : ℝ) := by
    dsimp [a]
    field_simp
  have hmean : (B.card : ℝ) * a ≤ ((tangents B).card : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hsize hapos
    rw [haeq] at hm
    linarith
  have hsumR : (∑ P ∈ B, (((tangents B).filter (ProjectiveIncident P)).card : ℝ)) =
      ((tangents B).card : ℝ) := by exact_mod_cast sum_tangencies B
  apply Finset.exists_le_of_sum_le hB
  calc
    (∑ _P ∈ B, a) = (B.card : ℝ) * a := by simp
    _ ≤ ((tangents B).card : ℝ) := hmean
    _ = ∑ P ∈ B, (((tangents B).filter (ProjectiveIncident P)).card : ℝ) := hsumR.symm

theorem skew_nonempty_of_card_le_order (B : Finset (ProjectivePoint F))
    (hB : B.card ≤ Fintype.card F) : (skewProjective B).Nonempty := by
  by_contra hempty
  have hnone : skewProjective B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  have hpos (l : ProjectiveLine F) :
      1 ≤ (B.filter (fun P => ProjectiveIncident P l)).card := by
    have hne : (B.filter (fun P => ProjectiveIncident P l)).card ≠ 0 := by
      intro hz
      have hm := (intersection_card_zero_iff B l).mp hz
      simp [hnone] at hm
    omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun l _ => hpos l)
  have hsum : (∑ l : ProjectiveLine F, (B.filter (fun P => ProjectiveIncident P l)).card) =
      (Fintype.card F + 1) * B.card := by
    apply sum_line_count ProjectiveIncident B (Fintype.card F + 1)
    intro P _
    exact card_projectivePencil P
  have hcard : Fintype.card (ProjectiveLine F) =
      Fintype.card F ^ 2 + Fintype.card F + 1 := by
    simp only [ProjectiveLine, Line, Direction, Fintype.card_option, Fintype.card_prod]
    ring
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, mul_one, hcard, hsum] at hs
  nlinarith

theorem card_skew_empty : (skewProjective (∅ : Finset (ProjectivePoint F))).card =
    Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp [skewProjective, ProjectiveLine, Line, Direction]
  ring

theorem nonempty_of_small_skew (B : Finset (ProjectivePoint F))
    (hskew : ((skewProjective B).card : ℝ) <
      (201 / 10000 : ℝ) * (Fintype.card F : ℝ) ^ 2) : B.Nonempty := by
  by_contra hB
  have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
  rw [he, card_skew_empty] at hskew
  push_cast at hskew
  nlinarith [sq_nonneg (Fintype.card F : ℝ), Nat.cast_nonneg (α := ℝ) (Fintype.card F)]

theorem exists_tangent_flag_with_margin (B : Finset (ProjectivePoint F)) (d : ℕ)
    (hq : (100 : ℝ) ≤ (Fintype.card F : ℝ)) (hB : B.card ≤ Fintype.card F)
    (hdegree : (d : ℝ) ^ 2 < 2 * ((skewProjective B).card : ℝ))
    (hskew : ((skewProjective B).card : ℝ) <
      (201 / 10000 : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    ∃ P ∈ B, ∃ ell ∈ tangents B, ProjectiveIncident P ell ∧
      (d : ℝ) + 1 < (((tangents B).filter (ProjectiveIncident P)).card : ℝ) := by
  have hBn := nonempty_of_small_skew B hskew
  obtain ⟨ell0, hell0⟩ := skew_nonempty_of_card_le_order B hB
  have hBR : (B.card : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hB
  obtain ⟨P, hPB, hP⟩ := exists_tangent_rich_point B hBn ell0 hell0 (by linarith)
  have hm := StabilityAffineArithmetic.tangent_margin hq hBR
    (Nat.cast_nonneg d) hdegree hskew
  have hstrict : (d : ℝ) + 1 <
      (((tangents B).filter (ProjectiveIncident P)).card : ℝ) := hm.trans_le hP
  have hpos : 0 < ((tangents B).filter (ProjectiveIncident P)).card := by
    have hposR : (0 : ℝ) < (((tangents B).filter (ProjectiveIncident P)).card : ℝ) := by
      linarith [Nat.cast_nonneg (α := ℝ) d]
    exact_mod_cast hposR
  obtain ⟨ell, hell⟩ := Finset.card_pos.mp hpos
  exact ⟨P, hPB, ell, (Finset.mem_filter.mp hell).1,
    (Finset.mem_filter.mp hell).2, hstrict⟩

end Balanced.StabilityTangents

end OAI
