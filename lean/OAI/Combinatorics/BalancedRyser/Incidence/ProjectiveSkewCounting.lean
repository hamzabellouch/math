import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Incidence.AffineMomentAlgebraLemmas
import OAI.Combinatorics.BalancedRyser.Incidence.Projective2

namespace OAI

namespace Balanced.ProjectiveSkewCounting

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem mem_skew_some_iff (U : Finset (Point F)) (D : Finset (Direction F))
    (d : Direction F) (b : F) :
    some (d, b) ∈ skewProjective (U.disjSum D) ↔
      d ∉ D ∧ b ∉ U.image (lineEval d) := by
  rw [skewProjective, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and,
    Sum.forall, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, ProjectiveIncident, ThroughProjective,
    OnLine, Finset.mem_image]
  constructor
  · rintro ⟨hU, hD⟩
    refine ⟨?_, ?_⟩
    · intro hd
      exact hD d hd rfl
    · rintro ⟨p, hp, hpb⟩
      exact hU p hp hpb
  · rintro ⟨hd, hb⟩
    refine ⟨?_, ?_⟩
    · intro p hp hpb
      exact hb ⟨p, hp, hpb⟩
    · intro e he hde
      exact hd (hde.symm ▸ he)

theorem mem_skew_none_iff (U : Finset (Point F)) (D : Finset (Direction F)) :
    none ∈ skewProjective (U.disjSum D) ↔ D = ∅ := by
  rw [skewProjective, Finset.mem_filter]
  simp [Sum.forall, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, ProjectiveIncident,
    Finset.eq_empty_iff_forall_notMem]

theorem missing_offsets_add_card (U : Finset (Point F)) (d : Direction F) :
    Fintype.card F ≤ (Finset.univ \ U.image (lineEval d)).card + U.card := by
  have himage := Finset.card_image_le (s := U) (f := lineEval d)
  have hpartition := Finset.card_sdiff_add_card_eq_card
    (show U.image (lineEval d) ⊆ Finset.univ from Finset.subset_univ _)
  rw [Finset.card_univ] at hpartition
  omega

theorem card_skew_disjSum (U : Finset (Point F)) (D : Finset (Direction F)) :
    (skewProjective (U.disjSum D)).card =
      (if D = ∅ then 1 else 0) +
        ∑ d ∈ Finset.univ \ D, (Finset.univ \ U.image (lineEval d)).card := by
  have hcount : (skewProjective (U.disjSum D)).card =
      ∑ l : ProjectiveLine F, if l ∈ skewProjective (U.disjSum D) then 1 else 0 := by
    simp
  rw [hcount, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [mem_skew_none_iff]
  congr 1
  simp only [mem_skew_some_iff, Finset.sdiff_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdD : d ∈ D
  · simp [hdD]
  · simp only [hdD, not_false_eq_true, true_and, ite_true]
    simp only [Finset.card_filter]

theorem missing_directions_mul_card_le (U : Finset (Point F))
    (D : Finset (Direction F)) :
    (Finset.univ \ D).card * Fintype.card F ≤
      (skewProjective (U.disjSum D)).card + (Finset.univ \ D).card * U.card := by
  have hs := Finset.sum_le_sum (s := Finset.univ \ D)
    (fun d _ => missing_offsets_add_card U d)
  simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib] at hs
  rw [card_skew_disjSum]
  omega

theorem missing_directions_mul_gap_le (U : Finset (Point F))
    (D : Finset (Direction F)) :
    ((Finset.univ \ D).card : ℝ) * ((Fintype.card F : ℝ) - U.card) ≤
      ((skewProjective (U.disjSum D)).card : ℝ) := by
  have h : ((Finset.univ \ D).card : ℝ) * (Fintype.card F : ℝ) ≤
      ((skewProjective (U.disjSum D)).card : ℝ) +
        ((Finset.univ \ D).card : ℝ) * (U.card : ℝ) := by
    exact_mod_cast missing_directions_mul_card_le U D
  nlinarith

omit [Field F] in

theorem missing_directions_add_card (D : Finset (Direction F)) :
    (Finset.univ \ D).card + D.card = Fintype.card F + 1 := by
  simpa [Direction] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)

theorem missing_le_two_skew_div (U : Finset (Point F))
    (D : Finset (Direction F))
    (hsize : 2 * (U.disjSum D).card + 3 * (Finset.univ \ D).card ≤
      3 * Fintype.card F + 2) :
    ((Finset.univ \ D).card : ℝ) ≤
      2 * ((skewProjective (U.disjSum D)).card : ℝ) / ((Fintype.card F : ℝ) + 1) := by
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) + 1 := by positivity
  by_cases hk : (Finset.univ \ D).card = 0
  · rw [hk]
    simp only [Nat.cast_zero]
    positivity
  have hpartition := missing_directions_add_card D
  rw [Finset.card_disjSum] at hsize
  have hsmall : 2 * U.card + 1 ≤ Fintype.card F := by omega
  have hsmallR : 2 * (U.card : ℝ) + 1 ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast hsmall
  have hgap := missing_directions_mul_gap_le U D
  have hproduct := mul_nonneg
    (show (0 : ℝ) ≤ ((Finset.univ \ D).card : ℝ) by positivity)
    (show (0 : ℝ) ≤ (Fintype.card F : ℝ) - 2 * U.card - 1 by linarith)
  apply (le_div_iff₀ hq).2
  nlinarith

theorem missing_le_two_skew_div_of_auxiliary_bound (U : Finset (Point F))
    (D : Finset (Direction F)) (t : ℕ)
    (hmissing : (Finset.univ \ D).card ≤ t)
    (hsize : 2 * (U.disjSum D).card + 3 * t ≤ 3 * Fintype.card F + 2) :
    ((Finset.univ \ D).card : ℝ) ≤
      2 * ((skewProjective (U.disjSum D)).card : ℝ) / ((Fintype.card F : ℝ) + 1) :=
  missing_le_two_skew_div U D (by omega)

theorem ideal_card_lower_bound (U : Finset (Point F))
    (D : Finset (Direction F))
    (hsize : 2 * (U.disjSum D).card + 3 * (Finset.univ \ D).card ≤
      3 * Fintype.card F + 2) :
    (Fintype.card F : ℝ) + 1 -
      2 * ((skewProjective (U.disjSum D)).card : ℝ) / ((Fintype.card F : ℝ) + 1) ≤
      (D.card : ℝ) := by
  have hmissing := missing_le_two_skew_div U D hsize
  have hpartition : ((Finset.univ \ D).card : ℝ) + (D.card : ℝ) =
      (Fintype.card F : ℝ) + 1 := by
    exact_mod_cast missing_directions_add_card D
  linarith

theorem ideal_card_source_bound (U : Finset (Point F)) (D : Finset (Direction F))
    (d : ℕ) (β : ℝ) (hβ : 0 < β)
    (hmissing : (Finset.univ \ D).card ≤ d)
    (hsize : ((U.disjSum D).card : ℝ) ≤
      (3 / 2 : ℝ) * ((Fintype.card F : ℝ) + 1) - β)
    (hdegree : (d : ℝ) ^ 2 < 2 * ((skewProjective (U.disjSum D)).card : ℝ))
    (hskew : ((skewProjective (U.disjSum D)).card : ℝ) <
      (2 / 9 : ℝ) * (β + 1) ^ 2) :
    (Fintype.card F : ℝ) -
      2 * ((skewProjective (U.disjSum D)).card : ℝ) / ((Fintype.card F : ℝ) + 1) ≤
      (D.card : ℝ) := by
  apply StabilityFinalArithmetic.collinear_lower_bound_of_source_bounds
    (Fintype.card F) U.card D.card (Finset.univ \ D).card d β
    ((skewProjective (U.disjSum D)).card : ℝ)
    (Fintype.card_pos_iff.mpr inferInstance) hβ (Nat.cast_nonneg _)
    (missing_directions_add_card D) hmissing
  · simpa only [Finset.card_disjSum] using hsize
  · exact hdegree
  · exact hskew
  · exact missing_directions_mul_gap_le U D

end Balanced.ProjectiveSkewCounting

end OAI
