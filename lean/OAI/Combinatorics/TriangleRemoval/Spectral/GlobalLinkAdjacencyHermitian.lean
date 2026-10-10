import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.EdgeIncidence
import OAI.Combinatorics.TriangleRemoval.Process.AveragingProjectorInftyOne
import OAI.Combinatorics.TriangleRemoval.Spectral.MatrixEuclideanAlgHom

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave
open scoped Matrix.Norms.Operator

theorem globalLinkAdjacency_hermitian {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) :
    (globalLinkAdjacency G hG).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [globalLinkAdjacency,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro u _
  exact (Matrix.isHermitian_mul_mul_conjTranspose (starInclusion (edgeStar G u))
    ((Matrix.isHermitian_reindex_iff _).mpr
      ((linkSimpleGraph G hG u).isHermitian_adjMatrix ℝ))).apply i j

theorem goodPrefix_semigroup_quantitative {n : ℕ} [NeZero n] {G : Graph n} [Nonempty G]
    {c C : ℝ} (h : GoodPrefixGraph n c C G) (hne : ∀ u, (neighbors G u).Nonempty)
    (hD : 1 ≤ prefixD n) (hδ : (n : ℝ)^(-c) ≤ 1)
    (T : ℝ) (hT : 0 ≤ T) (K : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ‖NormedSpace.exp ((-s) • ((prefixD n)⁻¹ • globalLinkAdjacency G h.1))‖ ≤
      (∑ j ∈ Finset.range K, ((1+2*T)*6*T)^j*(1+2*T)) +
      Real.sqrt G.card * ((2*prefixSpectralError n c*T)^K *
        Real.exp (T*(2*prefixSpectralError n c))) := by
  let P := globalStarAverage G
  let R := (prefixD n)⁻¹ • globalLinkAdjacency G h.1 - P
  let ε := 2*prefixSpectralError n c
  have hε : 0 ≤ ε := mul_nonneg (by norm_num)
    (prefixSpectralError_nonneg n c (le_trans zero_le_one hD))
  have hPR : P+R = (prefixD n)⁻¹ • globalLinkAdjacency G h.1 := by dsimp [R]; abel
  have hP : P.PosSemidef := globalStarAverage_posSemidef G
  have hR : IsSelfAdjoint R := by
    exact ((globalLinkAdjacency_hermitian G h.1).smul
      (isSelfAdjoint_iff.mpr rfl) |>.sub hP.isHermitian).isSelfAdjoint
  have hR₂ : ‖matrixEuclideanAlgHom R‖ ≤ ε := goodPrefix_global_spectral h hne hD hδ
  have hRinf : ‖R‖ ≤ 6 := goodPrefix_residual_infty h hD hδ
  have hF : Continuous (matrixEuclideanAlgHom (I := G)) :=
    (matrixEuclideanAlgHom (I := G)).toLinearMap.continuous_of_finiteDimensional
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖NormedSpace.exp ((-t) • P)‖ ≤ 1+2*T := by
    intro t ht
    have hdeg : ∀ u, 0 < currentDegree G u := fun u => Finset.card_pos.mpr (hne u)
    exact (graph_star_semigroup_bound G h.1 hdeg t ht.1).trans (by linarith [ht.2])
  have hb₂ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖NormedSpace.exp ((-t) • matrixEuclideanAlgHom P)‖ ≤ 1 :=
    fun t ht => euclidean_posSemidef_exp_bound P hP t ht.1
  have hf₂ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖NormedSpace.exp ((-t) • (matrixEuclideanAlgHom P + matrixEuclideanAlgHom R))‖ ≤
        Real.exp (T*ε) := by
    intro t ht
    apply (euclidean_perturbed_exp_bound P R hP hR t ht.1).trans
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left hR₂ ht.1).trans
      (mul_le_mul_of_nonneg_right ht.2 hε)
  let : CompleteSpace (EuclideanSpace ℝ G) := PiLp.completeSpace 2 (fun _ : G => ℝ)
  let : CompleteSpace (EuclideanSpace ℝ G →L[ℝ] EuclideanSpace ℝ G) :=
    ContinuousLinearMap.instCompleteSpace
  have hh := perturbation_mixed_norm_bound (matrixEuclideanAlgHom (I := G)) hF P R
    T (1+2*T) (Real.exp (T*ε)) (Real.sqrt G.card) hT (by positivity) (by positivity)
    (by positivity) (by simpa only [Fintype.card_coe] using
      (matrix_infty_le_sqrt_card_euclidean (I := G))) hb hb₂ hf₂ K s hs
  rw [hPR] at hh
  apply hh.trans
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    gcongr
  · gcongr

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
