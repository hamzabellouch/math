import OAI.Combinatorics.BalancedRyser.Incidence.ProjectiveNormalization
import OAI.Combinatorics.BalancedRyser.Incidence.SmallProjectiveArithmetic
import OAI.Combinatorics.BalancedRyser.Incidence.SmallProjectiveStabilityReduction
import OAI.Combinatorics.BalancedRyser.Incidence.StabilityAlgebraAssembly
import OAI.Combinatorics.BalancedRyser.Incidence.StabilityTangents

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]

theorem small_projective_line_refinement (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) (hB : B.card ≤ Fintype.card F)
    (hhalf : Fintype.card F + 1 ≤
      2 * (B.filter (fun P => ProjectiveIncident P ell)).card) :
    (Fintype.card F : ℝ) - 2 * ((skewProjective B).card : ℝ) /
      ((Fintype.card F : ℝ) + 1) ≤
        ((B.filter (fun P => ProjectiveIncident P ell)).card : ℝ) := by
  have hf : B.filter (fun P => ProjectiveIncident P ell) =
      B ∩ projectiveLinePoints ell := by ext P; simp
  rw [hf] at hhalf ⊢
  have hline : (B ∩ projectiveLinePoints ell).card +
      (projectiveLinePoints ell \ B).card = Fintype.card F + 1 := by
    rw [Finset.inter_comm B, Nat.add_comm, Finset.card_sdiff_add_card_inter,
      card_projectiveLinePoints]
  have hsize : (B \ projectiveLinePoints ell).card +
      (B ∩ projectiveLinePoints ell).card ≤ Fintype.card F := by
    rw [Finset.card_sdiff_add_card_inter]
    exact hB
  have hstrong := SmallProjectiveArithmetic.half_line_skew_refinement
    (Fintype.card F) (B ∩ projectiveLinePoints ell).card
    (B \ projectiveLinePoints ell).card (projectiveLinePoints ell \ B).card
    (skewProjective B).card hline hsize hhalf
    (missing_mul_order_sub_offLine_le_skew B ell)
  linarith

omit [Fintype F] in
theorem vertical_fiber_le_projective_section (U : Finset (Point F)) (c : F) :
    (U.filter (fun p => OnLine p (none,c))).card ≤
      ((U.disjSum {none}).filter
        (fun P => ProjectiveIncident P (some (none,c)))).card := by
  apply Finset.card_le_card_of_injOn Sum.inl
  · intro p hp
    obtain ⟨hpU, hpOn⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.inl_mem_disjSum.mpr hpU, hpOn⟩
  · intro p hp q hq h
    exact Sum.inl.inj h

theorem card_nonvertical_skew_codes_explicit (U : Finset (Point F)) :
    (StabilityPolynomial.nonverticalSkewCodes U).card =
      (Finset.univ.filter (fun z : Fin 2 → F =>
        ∀ p ∈ U, ¬ OnLine p (some (z 1), z 0))).card := by
  apply congrArg Finset.card
  ext z
  simp only [StabilityPolynomial.mem_nonverticalSkewCodes, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem small_projective_stability
    (hprime : Nat.Prime (Fintype.card F)) (hq : 100 ≤ Fintype.card F)
    (B : Finset (ProjectivePoint F)) (hB : B.card ≤ Fintype.card F)
    (hsmall : ((skewProjective B).card : ℝ) <
      (201 / 10000 : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    ∃ ell : ProjectiveLine F,
      (Fintype.card F : ℝ) - 2 * ((skewProjective B).card : ℝ) /
        ((Fintype.card F : ℝ) + 1) ≤
          ((B.filter (fun P => ProjectiveIncident P ell)).card : ℝ) := by
  classical
  have hδ : 0 < (skewProjective B).card :=
    Finset.card_pos.mpr (StabilityTangents.skew_nonempty_of_card_le_order B hB)
  obtain ⟨d, hd2, hdim⟩ :=
    SmallProjectiveArithmetic.exists_interpolation_degree (skewProjective B).card hδ
  have hdq := SmallProjectiveArithmetic.three_degree_lt_order hsmall hd2
  obtain ⟨P, hPB, ell, hell, hPell, hrich⟩ :=
    StabilityTangents.exists_tangent_flag_with_margin B d (by exact_mod_cast hq) hB
      (by exact_mod_cast hd2) hsmall
  have hsingle : B.filter (fun Q => ProjectiveIncident Q ell) = {P} := by
    obtain ⟨Q, hQ⟩ := Finset.card_eq_one.mp ((StabilityTangents.mem_tangents B ell).mp hell)
    have hPQ : P = Q := by
      have hm : P ∈ B.filter (fun Q => ProjectiveIncident Q ell) :=
        Finset.mem_filter.mpr ⟨hPB, hPell⟩
      rw [hQ] at hm
      exact Finset.mem_singleton.mp hm
    simpa [hPQ] using hQ
  obtain ⟨e, U, heP, heell, heU, hUcard, hskew, htangent⟩ :=
    ProjectiveNormalization.exists_normalized_affine_set_with_tangents B P ell hsingle
  have hU : U.card ≤ Fintype.card F := by omega
  have hcodes : (StabilityPolynomial.nonverticalSkewCodes U).card =
      (skewProjective B).card := (card_nonvertical_skew_codes_explicit U).trans hskew
  have hempty : d < (Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c).card := by
    have ht : ((StabilityTangents.tangents B).filter (ProjectiveIncident P)).card =
        (Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c).card + 1 := by
      simpa only [StabilityTangents.tangents, Finset.filter_filter,
        and_comm] using htangent
    rw [ht] at hrich
    have hn : d + 1 < (Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c).card + 1 := by
      exact_mod_cast hrich
    omega
  obtain ⟨c, hc⟩ := StabilityPolynomial.normalized_prime_stability hprime U d hU
    (by rw [hcodes]; exact hdim) (by omega) (by simpa only using hempty)
  let m : ProjectiveLine F := some (none,c)
  let old : ProjectiveLine F := e.line.symm m
  have htransport : ((U.disjSum {none}).filter
      (fun Q => ProjectiveIncident Q m)).card =
        (B.filter (fun Q => ProjectiveIncident Q old)).card := by
    have ht := ProjectiveNormalization.card_filter_incident e B old
    simpa only [old, Equiv.apply_symm_apply, heU] using ht
  have hlarge : Fintype.card F - d ≤
      (B.filter (fun Q => ProjectiveIncident Q old)).card := by
    rw [← htransport]
    simpa only [m] using hc.trans (vertical_fiber_le_projective_section U c)
  refine ⟨old, small_projective_line_refinement B old hB ?_⟩
  exact SmallProjectiveArithmetic.half_line_of_degree_bound hdq hlarge

end Balanced

end OAI
