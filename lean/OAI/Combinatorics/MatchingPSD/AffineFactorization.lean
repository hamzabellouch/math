import Mathlib
import OAI.Combinatorics.MatchingPSD.AffineCertificate
import OAI.Combinatorics.MatchingPSD.AffineSlacks
import OAI.Combinatorics.MatchingPSD.TightMatchings
import OAI.Combinatorics.MatchingPSD.NormalizedFactors

namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing Finset Matrix
open scoped BigOperators

theorem affineLift_hasFactorization {n r : ℕ} (hn : 4 ≤ n) (he : Even n)
    (h : HasAffineLift n r) : HasFactorization n r := by
  classical
  obtain ⟨L, T, hT⟩ := h
  have hvertex (M : PerfectMatching n) : ∃ X : Matrix (Fin r) (Fin r) ℝ,
      X ∈ L ∧ X.PosSemidef ∧ T X = matchingPoint M := by
    have hm : matchingPoint M ∈ matchingPolytope n :=
      subset_convexHull ℝ _ (Set.mem_range_self M)
    rw [← hT] at hm
    obtain ⟨X, hX, heq⟩ := hm
    exact ⟨X, hX.1, hX.2, heq⟩
  choose B hBL hB hBT using hvertex
  have hrow (i : Row n) : ∃ A : Matrix (Fin r) (Fin r) ℝ,
      A.PosSemidef ∧ ∀ M, (A * B M).trace = slack i M := by
    obtain ⟨M₀, hzero⟩ := row_has_tight_matching hn he i
    have hnonneg (X : Matrix (Fin r) (Fin r) ℝ) (hXL : X ∈ L)
        (hXP : X.PosSemidef) : 0 ≤ ((slackAffine i).comp T) X := by
      apply slackAffine_nonneg
      rw [← hT]
      exact ⟨X, ⟨hXL, hXP⟩, rfl⟩
    have hz : ((slackAffine i).comp T) (B M₀) = 0 := by
      simpa only [AffineMap.comp_apply, hBT, slackAffine_vertex] using hzero
    obtain ⟨A, hA, hAB⟩ := AffinePSD.affine_slack_certificate L B hB hBL
      ((slackAffine i).comp T) hnonneg M₀ hz
    refine ⟨A, hA, fun M => ?_⟩
    simpa only [AffineMap.comp_apply, hBT, slackAffine_vertex] using hAB M
  choose A hA hAB using hrow
  exact ⟨A, B, hA, hB, fun i M => (hAB i M).symm⟩

lemma factorization_order_pos {n r : ℕ} (hn : 1 ≤ n) (he : Even n)
    (h : HasFactorization n r) : 0 < r := by
  classical
  by_contra hr
  have hr0 : r = 0 := by omega
  subst r
  obtain ⟨M⟩ := perfectMatching_nonempty he
  let v : Fin n := ⟨0, by omega⟩
  have hc := M.2 v
  obtain ⟨e, heq⟩ := Finset.card_eq_one.mp hc
  have heM : e ∈ M.1 := (Finset.mem_filter.mp (heq.symm ▸ Finset.mem_singleton_self e)).1
  obtain ⟨A, B, hA, hB, hf⟩ := h
  have hz := hf (Sum.inl e) M
  simp [slack, heM, Matrix.trace] at hz

end PerfectMatchingPSD

end OAI
