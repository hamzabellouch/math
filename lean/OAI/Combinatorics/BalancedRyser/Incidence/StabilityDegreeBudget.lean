import OAI.Combinatorics.BalancedRyser.Incidence.SmallProjectiveStability
import OAI.Combinatorics.BalancedRyser.Incidence.StabilityFinalRefinement

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open scoped Classical

variable {F : Type*} [Field F] [Fintype F]

theorem projective_large_section_of_tangent_degree_budget
    (hprime : Nat.Prime (Fintype.card F))
    (B : Finset (ProjectivePoint F)) (P : ProjectivePoint F)
    (ell : ProjectiveLine F) (d s : ℕ)
    (hsingle : B.filter (fun Q => ProjectiveIncident Q ell) = {P})
    (hrich : d + 1 < ((StabilityTangents.tangents B).filter (ProjectiveIncident P)).card)
    (hsize : 2 * (skewProjective B).card < (d + 1) * (d + 2))
    (hbudget : B.card + d ≤ Fintype.card F + s + 1)
    (hgap : 2 * s + d < Fintype.card F + 1) :
    ∃ m : ProjectiveLine F, (projectiveLinePoints m \ B).card ≤ d := by
  classical
  obtain ⟨e, U, _heP, _heell, heU, hUcard, hskew, htangent⟩ :=
    ProjectiveNormalization.exists_normalized_affine_set_with_tangents B P ell hsingle
  have hcodes : (StabilityPolynomial.nonverticalSkewCodes U).card =
      (skewProjective B).card := (card_nonvertical_skew_codes_explicit U).trans hskew
  have ht : ((StabilityTangents.tangents B).filter (ProjectiveIncident P)).card =
      (Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c).card + 1 := by
    simpa only [StabilityTangents.tangents, Finset.filter_filter, and_comm] using htangent
  have hempty : d < (Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c).card := by
    rw [ht] at hrich
    omega
  obtain ⟨c, hc⟩ := StabilityPolynomial.normalized_prime_stability_of_degree_budget
    hprime U d s (by rw [hcodes]; exact hsize) (by omega) hgap
      (by simpa only using hempty)
  let m : ProjectiveLine F := some (none, c)
  let old : ProjectiveLine F := e.line.symm m
  have htransport : ((U.disjSum {none}).filter
      (fun Q => ProjectiveIncident Q m)).card =
        (B.filter (fun Q => ProjectiveIncident Q old)).card := by
    have ht' := ProjectiveNormalization.card_filter_incident e B old
    simpa only [old, Equiv.apply_symm_apply, heU] using ht'
  have hsection : (B.filter (fun Q => ProjectiveIncident Q old)).card =
      (U.filter (fun p => OnLine p (none, c))).card + 1 := by
    have hfiber : U.filter (fun point => OnLine point (none, c)) =
        U.filter (fun point => point.1 = c) :=
      Finset.filter_congr fun point _ => Iff.rfl
    rw [← htransport, hfiber]
    exact ProjectiveNormalization.card_normalized_vertical_section U c
  have hpartition : (projectiveLinePoints old \ B).card +
      (B.filter (fun Q => ProjectiveIncident Q old)).card = Fintype.card F + 1 := by
    have hf : B.filter (fun Q => ProjectiveIncident Q old) =
        B ∩ projectiveLinePoints old := by ext Q; simp
    rw [hf, Finset.inter_comm B, Finset.card_sdiff_add_card_inter,
      card_projectiveLinePoints]
  refine ⟨old, ?_⟩
  rw [hsection] at hpartition
  omega

theorem projective_source_refinement_of_tangent_degree_budget
    (hprime : Nat.Prime (Fintype.card F))
    (B : Finset (ProjectivePoint F)) (P : ProjectivePoint F)
    (ell : ProjectiveLine F) (d s : ℕ) (β : ℝ) (hβ : 0 < β)
    (hsingle : B.filter (fun Q => ProjectiveIncident Q ell) = {P})
    (hrich : d + 1 < ((StabilityTangents.tangents B).filter (ProjectiveIncident P)).card)
    (hdim : 2 * (skewProjective B).card < (d + 1) * (d + 2))
    (hbudget : B.card + d ≤ Fintype.card F + s + 1)
    (hgap : 2 * s + d < Fintype.card F + 1)
    (hsize : (B.card : ℝ) ≤ (3 / 2 : ℝ) * ((Fintype.card F : ℝ) + 1) - β)
    (hdegree : (d : ℝ) ^ 2 < 2 * ((skewProjective B).card : ℝ))
    (hskew : ((skewProjective B).card : ℝ) < (2 / 9 : ℝ) * (β + 1) ^ 2) :
    ∃ m : ProjectiveLine F,
      (Fintype.card F : ℝ) - 2 * ((skewProjective B).card : ℝ) /
        ((Fintype.card F : ℝ) + 1) ≤
          ((B.filter (fun Q => ProjectiveIncident Q m)).card : ℝ) := by
  classical
  obtain ⟨m, hm⟩ := projective_large_section_of_tangent_degree_budget
    hprime B P ell d s hsingle hrich hdim hbudget hgap
  exact ⟨m, projective_line_source_refinement B m d β hβ hm hsize hdegree hskew⟩

theorem projective_large_section_of_nonblocking_degree_budget
    (hprime : Nat.Prime (Fintype.card F))
    (B : Finset (ProjectivePoint F)) (hB : B.Nonempty)
    (hskew : (skewProjective B).Nonempty) (d s : ℕ)
    (hsize : (B.card : ℝ) ≤ (3 / 2 : ℝ) * ((Fintype.card F : ℝ) + 1))
    (hmargin : (d : ℝ) + 1 < (2 / 3 : ℝ) *
      (2 * (Fintype.card F : ℝ) - B.card -
        2 * ((skewProjective B).card : ℝ) / ((Fintype.card F : ℝ) + 1)))
    (hdim : 2 * (skewProjective B).card < (d + 1) * (d + 2))
    (hbudget : B.card + d ≤ Fintype.card F + s + 1)
    (hgap : 2 * s + d < Fintype.card F + 1) :
    ∃ m : ProjectiveLine F, (projectiveLinePoints m \ B).card ≤ d := by
  classical
  obtain ⟨ell0, hell0⟩ := hskew
  obtain ⟨P, hPB, hP⟩ :=
    StabilityTangents.exists_tangent_rich_point B hB ell0 hell0 hsize
  have hrich : d + 1 <
      ((StabilityTangents.tangents B).filter (ProjectiveIncident P)).card := by
    exact_mod_cast hmargin.trans_le hP
  have hpositive : 0 <
      ((StabilityTangents.tangents B).filter (ProjectiveIncident P)).card := by omega
  obtain ⟨ell, hell⟩ := Finset.card_pos.mp hpositive
  have hell' := (Finset.mem_filter.mp hell).1
  have hPell := (Finset.mem_filter.mp hell).2
  have hsingle : B.filter (fun Q => ProjectiveIncident Q ell) = {P} := by
    obtain ⟨Q, hQ⟩ := Finset.card_eq_one.mp
      ((StabilityTangents.mem_tangents B ell).mp hell')
    have hPQ : P = Q := by
      have hm : P ∈ B.filter (fun Q => ProjectiveIncident Q ell) :=
        Finset.mem_filter.mpr ⟨hPB, hPell⟩
      rw [hQ] at hm
      exact Finset.mem_singleton.mp hm
    simpa only [hPQ] using hQ
  exact projective_large_section_of_tangent_degree_budget
    hprime B P ell d s hsingle hrich hdim hbudget hgap

end Balanced

end OAI
