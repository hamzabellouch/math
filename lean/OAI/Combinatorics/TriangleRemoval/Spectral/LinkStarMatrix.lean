import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.GoodPrefixStarApproximation
import OAI.Combinatorics.TriangleRemoval.Process.ReindexQuadratic
import OAI.Combinatorics.TriangleRemoval.Spectral.EdgeStar

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave
open scoped Matrix.Norms.L2Operator

theorem averagingProjector_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) : Matrix.reindex e e (averagingProjector : Matrix I I ℝ) =
      (averagingProjector : Matrix J J ℝ) := by
  ext i j
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,averagingProjector]
  rw [Fintype.card_congr e]

theorem averagingProjector_hermitian {I : Type*} [Fintype I] :
    (averagingProjector : Matrix I I ℝ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [averagingProjector]

theorem averagingProjector_posSemidef {I : Type*} [Fintype I] :
    (averagingProjector : Matrix I I ℝ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg averagingProjector_hermitian
  intro x
  have heq : star x ⬝ᵥ ((averagingProjector : Matrix I I ℝ) *ᵥ x) =
      (Fintype.card I : ℝ)⁻¹ * (∑ i, x i)^2 := by
    simp [averagingProjector,dotProduct,Matrix.mulVec,← Finset.sum_mul,pow_two,
      mul_comm,mul_assoc]
  rw [heq]
  positivity

noncomputable def linkStarMatrix {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    Matrix (edgeStar G u) (edgeStar G u) ℝ :=
  Matrix.reindex (neighborEdgeEquiv G hG u) (neighborEdgeEquiv G hG u)
    ((linkSimpleGraph G hG u).adjMatrix ℝ)

noncomputable def globalLinkAdjacency {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) :
    Matrix G G ℝ := ∑ u, extendStar (edgeStar G u) (linkStarMatrix G hG u)

noncomputable def globalStarAverage {n : ℕ} (G : Graph n) : Matrix G G ℝ :=
  ∑ u, extendStar (edgeStar G u) averagingProjector

theorem globalStarAverage_posSemidef {n : ℕ} (G : Graph n) :
    (globalStarAverage G).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro u _
  exact averagingProjector_posSemidef.mul_mul_conjTranspose_same _

noncomputable def prefixSpectralError (n : ℕ) (c : ℝ) : ℝ :=
  4 * ((8001 : ℝ) * (n : ℝ)^(-c) + (8000 : ℝ)^8001 * 2^8000 *
    ((n : ℝ) / prefixD n^4000 + 1/prefixD n)) ^ (1 / (8000 : ℝ)) + 7*(n : ℝ)^(-c)

theorem prefixSpectralError_nonneg (n : ℕ) (c : ℝ) (hD : 0 ≤ prefixD n) :
    0 ≤ prefixSpectralError n c := by
  unfold prefixSpectralError
  positivity

theorem goodPrefix_global_spectral {n : ℕ} {G : Graph n} {c C : ℝ}
    (h : GoodPrefixGraph n c C G) (hne : ∀ u, (neighbors G u).Nonempty)
    (hD : 1 ≤ prefixD n) (hδ : (n : ℝ)^(-c) ≤ 1) :
    ‖(prefixD n)⁻¹ • globalLinkAdjacency G h.1 - globalStarAverage G‖ ≤
      2 * prefixSpectralError n c := by
  let M (u : Fin n) : Matrix (neighbors G u) (neighbors G u) ℝ :=
    (prefixD n)⁻¹ • (linkSimpleGraph G h.1 u).adjMatrix ℝ - averagingProjector
  let N (u : Fin n) : Matrix (edgeStar G u) (edgeStar G u) ℝ :=
    Matrix.reindex (neighborEdgeEquiv G h.1 u) (neighborEdgeEquiv G h.1 u) (M u)
  have hM : ∀ u, (M u).IsHermitian := by
    intro u
    exact ((linkSimpleGraph G h.1 u).isHermitian_adjMatrix ℝ).smul
      (isSelfAdjoint_iff.mpr rfl) |>.sub averagingProjector_hermitian
  have hlocal : ∀ u, ‖N u‖ ≤ prefixSpectralError n c := by
    intro u
    have : Nonempty (neighbors G u) := (hne u).to_subtype
    apply (hermitian_reindex_norm_le _ _ (hM u)).trans
    apply (goodPrefix_star_fixed h u hD hδ).trans
    have hn : ((neighbors G u).card : ℝ) ≤ n := by
      exact_mod_cast (show (neighbors G u).card ≤ n by simpa using (neighbors G u).card_le_univ)
    unfold prefixSpectralError
    gcongr
  have hsplit : (prefixD n)⁻¹ • globalLinkAdjacency G h.1 - globalStarAverage G =
      ∑ u, extendStar (edgeStar G u) (N u) := by
    simp only [globalLinkAdjacency,globalStarAverage,Finset.smul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    have heq : N u = (prefixD n)⁻¹ • linkStarMatrix G h.1 u - averagingProjector := by
      ext i j
      simp only [N,M,linkStarMatrix,Matrix.reindex_apply,Matrix.submatrix_apply,
        Matrix.sub_apply,Matrix.smul_apply,averagingProjector]
      rw [Fintype.card_congr (neighborEdgeEquiv G h.1 u)]
    rw [heq]
    simp [extendStar,Matrix.mul_sub,Matrix.sub_mul,Matrix.smul_mul,Matrix.mul_smul]
  rw [hsplit]
  apply graph_star_error_norm G h.1 N (fun u => (Matrix.isHermitian_reindex_iff _).mpr (hM u))
    (prefixSpectralError n c) (prefixSpectralError_nonneg n c (le_trans zero_le_one hD)) hlocal

end SharpTerminalLeave

end
end

end OAI
