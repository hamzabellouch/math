import OAI.Combinatorics.BalancedRyser.Incidence.StabilityDegreeBudget

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]

theorem global_projective_tangent_count (B : Finset (ProjectivePoint F)) :
    2 * (Fintype.card F ^ 2 + Fintype.card F + 1) ≤
      B.card * (Fintype.card F + 1) + 2 * (skewProjective B).card +
        (StabilityTangents.tangents B).card := by
  classical
  have hcount := StabilityTangents.twice_card_le_intersections_and_small B Finset.univ
  have hskew : Finset.univ.filter (fun l => l ∈ skewProjective B) = skewProjective B := by
    ext l
    simp
  have htangent : Finset.univ.filter (fun l => l ∈ StabilityTangents.tangents B) =
      StabilityTangents.tangents B := by
    ext l
    simp
  have hsum : (∑ l : ProjectiveLine F,
      (B.filter (fun P => ProjectiveIncident P l)).card) =
        (Fintype.card F + 1) * B.card := by
    apply sum_line_count ProjectiveIncident B (Fintype.card F + 1)
    intro P _
    exact card_projectivePencil P
  have hcard : Fintype.card (ProjectiveLine F) =
      Fintype.card F ^ 2 + Fintype.card F + 1 := by
    simp only [ProjectiveLine, Line, Direction, Fintype.card_option, Fintype.card_prod]
    ring
  rw [hskew, htangent, hsum, Finset.card_univ, hcard] at hcount
  simpa only [Nat.mul_comm (Fintype.card F + 1) B.card] using hcount

private theorem tangent_card_gt_set_card (q b t : ℕ)
    (hprime : Nat.Prime q) (hq : 3 ≤ q) (hsize : 2 * b < 3 * (q + 1))
    (hcount : 2 * (q ^ 2 + q + 1) ≤ b * (q + 1) + t) : b < t := by
  by_contra hn
  have ht : t ≤ b := by omega
  by_cases hq3 : q = 3
  · subst q
    have hb : b ≤ 5 := by omega
    nlinarith
  have hq4 : q ≠ 4 := by
    intro he
    norm_num [he] at hprime
  have hq5 : 5 ≤ q := by omega
  have hb : 2 * b ≤ 3 * q + 2 := by omega
  have hmul := Nat.mul_le_mul_left (q + 2) hb
  have hstrict : 4 * q < q * q :=
    Nat.mul_lt_mul_of_pos_right (by omega : 4 < q) (by omega : 0 < q)
  nlinarith

theorem blocking_set_has_two_tangents
    (hprime : Nat.Prime (Fintype.card F)) (hq : 3 ≤ Fintype.card F)
    (B : Finset (ProjectivePoint F)) (hskew : skewProjective B = ∅)
    (hsize : 2 * B.card < 3 * (Fintype.card F + 1)) :
    ∃ P ∈ B, 1 < ((StabilityTangents.tangents B).filter (ProjectiveIncident P)).card := by
  classical
  have hcount := global_projective_tangent_count B
  rw [hskew] at hcount
  simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero] at hcount
  have hlarge := tangent_card_gt_set_card (Fintype.card F) B.card
    (StabilityTangents.tangents B).card hprime hq hsize hcount
  by_contra! hnone
  have hsum := Finset.sum_le_sum (s := B) (fun P hP => hnone P hP)
  rw [StabilityTangents.sum_tangencies B] at hsum
  simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one] at hsum
  omega

private theorem blocking_full_line_of_tangencies
    (hprime : Nat.Prime (Fintype.card F))
    (B : Finset (ProjectivePoint F)) (hskew : skewProjective B = ∅)
    (hsize : 2 * B.card < 3 * (Fintype.card F + 1))
    (htangencies : ∃ P ∈ B,
      1 < ((StabilityTangents.tangents B).filter (ProjectiveIncident P)).card) :
    ∃ m : ProjectiveLine F, projectiveLinePoints m ⊆ B := by
  classical
  obtain ⟨P, hPB, hrich⟩ := htangencies
  have hpositive : 0 <
      ((StabilityTangents.tangents B).filter (ProjectiveIncident P)).card := by omega
  obtain ⟨ell, hell⟩ := Finset.card_pos.mp hpositive
  have hPell := (Finset.mem_filter.mp hell).2
  have hsingle : B.filter (fun Q => ProjectiveIncident Q ell) = {P} := by
    obtain ⟨Q, hQ⟩ := Finset.card_eq_one.mp
      ((StabilityTangents.mem_tangents B ell).mp (Finset.mem_filter.mp hell).1)
    have hPQ : P = Q := by
      have hm : P ∈ B.filter (fun Q => ProjectiveIncident Q ell) :=
        Finset.mem_filter.mpr ⟨hPB, hPell⟩
      rw [hQ] at hm
      exact Finset.mem_singleton.mp hm
    simpa only [hPQ] using hQ
  obtain ⟨m, hm⟩ := projective_large_section_of_tangent_degree_budget
    hprime B P ell 0 (B.card - 1 - Fintype.card F) hsingle (by simpa using hrich)
      (by simp [hskew]) (by omega) (by omega)
  exact ⟨m, Finset.sdiff_eq_empty_iff_subset.mp
    (Finset.card_eq_zero.mp (by omega))⟩

theorem small_prime_blocking_set_contains_line
    (hprime : Nat.Prime (Fintype.card F)) (hq : 3 ≤ Fintype.card F)
    (B : Finset (ProjectivePoint F)) (hskew : skewProjective B = ∅)
    (hsize : 2 * B.card < 3 * (Fintype.card F + 1)) :
    ∃ m : ProjectiveLine F, projectiveLinePoints m ⊆ B :=
  blocking_full_line_of_tangencies hprime B hskew hsize
    (blocking_set_has_two_tangents hprime hq B hskew hsize)

theorem order_two_blocking_set_contains_line
    (hq : Fintype.card F = 2)
    (B : Finset (ProjectivePoint F)) (hskew : skewProjective B = ∅)
    (hsize : 2 * B.card < 3 * (Fintype.card F + 1)) :
    ∃ m : ProjectiveLine F, projectiveLinePoints m ⊆ B := by
  classical
  have hprime : Nat.Prime (Fintype.card F) := by rw [hq]; norm_num
  have hcount := global_projective_tangent_count B
  rw [hq, hskew] at hcount
  simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero] at hcount
  have hb : B.card ≤ 4 := by omega
  by_cases hbsmall : B.card ≤ 3
  · apply blocking_full_line_of_tangencies hprime B hskew hsize
    by_contra! hnone
    have hsum := Finset.sum_le_sum (s := B) (fun P hP => hnone P hP)
    rw [StabilityTangents.sum_tangencies B] at hsum
    simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one] at hsum
    nlinarith
  have hb4 : B.card = 4 := by omega
  have htpos : 0 < (StabilityTangents.tangents B).card := by nlinarith
  obtain ⟨ell, hell⟩ := Finset.card_pos.mp htpos
  obtain ⟨P, hsingle⟩ := Finset.card_eq_one.mp
    ((StabilityTangents.mem_tangents B ell).mp hell)
  obtain ⟨e, U, _heP, _heell, heU, hUcard, _hcodes⟩ :=
    ProjectiveNormalization.exists_normalized_affine_set B P ell hsingle
  have hU3 : U.card = 3 := by omega
  have hsum : U.card = ∑ c : F, (U.filter (fun p => p.1 = c)).card := by
    exact Finset.card_eq_sum_card_fiberwise (s := U) (t := Finset.univ)
      (f := fun p : Point F => p.1) (fun _ _ => Finset.mem_univ _)
  have hsumlt : (∑ _c : F, 1) < ∑ c : F, (U.filter (fun p => p.1 = c)).card := by
    rw [← hsum]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_one, hq, hU3]
    omega
  obtain ⟨c, _hc, hlarge⟩ := Finset.exists_lt_of_sum_lt hsumlt
  let m : ProjectiveLine F := some (none, c)
  let old : ProjectiveLine F := e.line.symm m
  have htransport : ((U.disjSum {none}).filter
      (fun Q => ProjectiveIncident Q m)).card =
        (B.filter (fun Q => ProjectiveIncident Q old)).card := by
    have ht := ProjectiveNormalization.card_filter_incident e B old
    simpa only [old, Equiv.apply_symm_apply, heU] using ht
  have hsection : (B.filter (fun Q => ProjectiveIncident Q old)).card =
      (U.filter (fun p => p.1 = c)).card + 1 := by
    rw [← htransport]
    exact ProjectiveNormalization.card_normalized_vertical_section U c
  have hpartition : (projectiveLinePoints old \ B).card +
      (B.filter (fun Q => ProjectiveIncident Q old)).card = Fintype.card F + 1 := by
    have hf : B.filter (fun Q => ProjectiveIncident Q old) =
        B ∩ projectiveLinePoints old := by ext Q; simp
    rw [hf, Finset.inter_comm B, Finset.card_sdiff_add_card_inter,
      card_projectiveLinePoints]
  refine ⟨old, Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp ?_)⟩
  omega

theorem prime_blocking_set_contains_line
    (hprime : Nat.Prime (Fintype.card F))
    (B : Finset (ProjectivePoint F)) (hskew : skewProjective B = ∅)
    (hsize : 2 * B.card < 3 * (Fintype.card F + 1)) :
    ∃ m : ProjectiveLine F, projectiveLinePoints m ⊆ B := by
  by_cases hq : Fintype.card F = 2
  · exact order_two_blocking_set_contains_line hq B hskew hsize
  · have hq3 : 3 ≤ Fintype.card F := by have := hprime.two_le; omega
    exact small_prime_blocking_set_contains_line hprime hq3 B hskew hsize

theorem source_zero_skew_contains_line
    (hprime : Nat.Prime (Fintype.card F))
    (B : Finset (ProjectivePoint F)) (β : ℝ) (hβ : 0 < β)
    (hskew : skewProjective B = ∅)
    (hsize : (B.card : ℝ) ≤ (3 / 2 : ℝ) * ((Fintype.card F : ℝ) + 1) - β) :
    ∃ m : ProjectiveLine F, projectiveLinePoints m ⊆ B := by
  apply prime_blocking_set_contains_line hprime B hskew
  have hR : ((2 * B.card : ℕ) : ℝ) < ((3 * (Fintype.card F + 1) : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hR

end Balanced

end OAI
