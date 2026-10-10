import Mathlib
import OAI.Combinatorics.MatchingPSD.AffineModel
import OAI.Combinatorics.MatchingPSD.FiniteFactorization

namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing Finset Matrix
open scoped BigOperators

noncomputable def slackAffine {n : ℕ} (i : Row n) : (Edge n → ℝ) →ᵃ[ℝ] ℝ := by
  classical
  cases i with
  | inl e => exact (LinearMap.proj e).toAffineMap
  | inr U =>
    exact (∑ e : Edge n, if Crosses U.1 e then LinearMap.proj e else 0).toAffineMap -
      AffineMap.const ℝ (Edge n → ℝ) 1

lemma slackAffine_vertex {n : ℕ} (i : Row n) (M : PerfectMatching n) :
    slackAffine i (matchingPoint M) = slack i M := by
  classical
  cases i with
  | inl e => rfl
  | inr U =>
    simp only [slackAffine, AffineMap.coe_sub, Pi.sub_apply, AffineMap.const_apply,
      LinearMap.coe_toAffineMap, slack]
    congr 1
    rw [LinearMap.sum_apply]
    calc
      _ = ∑ e : Edge n, if Crosses U.1 e ∧ e ∈ M.1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : Crosses U.1 e <;> simp [h, matchingPoint]
      _ = _ := by
        simp only [Finset.sum_boole, crossingCount]
        apply congrArg (fun s : Finset (Edge n) => (s.card : ℝ))
        ext e
        simp [and_comm]

lemma slackAffine_nonneg {n : ℕ} (i : Row n) {x : Edge n → ℝ}
    (hx : x ∈ matchingPolytope n) : 0 ≤ slackAffine i x := by
  have hc : Convex ℝ {x : Edge n → ℝ | 0 ≤ slackAffine i x} := by
    exact (convex_Ici (0 : ℝ)).affine_preimage (slackAffine i)
  apply convexHull_min _ hc hx
  rintro _ ⟨M, rfl⟩
  rw [Set.mem_ofPred_eq, slackAffine_vertex]
  exact slack_nonneg i M

end PerfectMatchingPSD

end OAI
