import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixCodegreeDriftTerm
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixBalancedNoise
import OAI.Combinatorics.TriangleRemoval.Spectral.WheelSpoke
import OAI.Combinatorics.TriangleRemoval.Embeddings.DegreeTemplate

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Filter Classical

namespace SharpTerminalLeave

theorem density_global_spectral {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (D c : ℝ) (hD : prefixD n ≤ D) (hDmin : 1 ≤ prefixD n)
    (hδ : (n : ℝ)^(-c) ≤ 1) (hne : ∀ u, (neighbors G u).Nonempty)
    (hrow : ∀ u v : Fin n, {u,v} ∈ G →
      |(currentCodegree G u v : ℝ)-D| ≤ (n : ℝ)^(-c)*D)
    (hcyc : ∀ j, 3 ≤ j → j ≤ 8000 → ∀ u : Fin n,
      |linkCycleCount j G u-D^j| ≤ (n : ℝ)^(-c)*D^j) :
    ‖D⁻¹ • globalLinkAdjacency G hG-globalStarAverage G‖ ≤ 2*prefixSpectralError n c := by
  have hD1 : 1 ≤ D := hDmin.trans hD
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hd0 : 0 ≤ (n : ℝ)^(-c) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let M (u : Fin n) : Matrix (neighbors G u) (neighbors G u) ℝ :=
    D⁻¹ • (linkSimpleGraph G hG u).adjMatrix ℝ-averagingProjector
  let N (u : Fin n) : Matrix (edgeStar G u) (edgeStar G u) ℝ :=
    Matrix.reindex (neighborEdgeEquiv G hG u) (neighborEdgeEquiv G hG u) (M u)
  have hM : ∀ u, (M u).IsHermitian := by
    intro u
    exact ((linkSimpleGraph G hG u).isHermitian_adjMatrix ℝ).smul
      (isSelfAdjoint_iff.mpr rfl) |>.sub averagingProjector_hermitian
  have hlocal : ∀ u, ‖N u‖ ≤ prefixSpectralError n c := by
    intro u
    have : Nonempty (neighbors G u) := (hne u).to_subtype
    apply (hermitian_reindex_norm_le _ _ (hM u)).trans
    have hr : ∀ v : neighbors G u,
        |((Finset.univ.filter ((linkSimpleGraph G hG u).Adj v)).card : ℝ)-D| ≤ (n : ℝ)^(-c)*D := by
      intro v
      rw [link_degree_eq G hG u v]
      exact hrow u v.val (Finset.mem_filter.mp v.property).2
    have hm := hcyc 8000 (by decide) le_rfl u
    rw [linkCycleCount_eq_graphEmbeddings (j := 7998) G hG u] at hm
    have hc : ∀ b, 3 ≤ b → b < 8000 →
        ((graphEmbeddings (SimpleGraph.cycleGraph b) (linkSimpleGraph G hG u)).card : ℝ) ≤ 2*D^b := by
      intro b hb hb'
      have hh := (abs_le.mp (hcyc b hb hb'.le u)).2
      have he : b = b-2+2 := by omega
      have hcount : linkCycleCount b G u =
          ((graphEmbeddings (SimpleGraph.cycleGraph b) (linkSimpleGraph G hG u)).card : ℝ) := by
        rw [he]
        exact linkCycleCount_eq_graphEmbeddings G hG u
      rw [hcount] at hh
      have hx := mul_le_mul_of_nonneg_right hδ (pow_nonneg hD0.le b)
      nlinarith
    have hh := graph_star_approximation (linkSimpleGraph G hG u) 7997 (by decide)
      D ((n : ℝ)^(-c)) hD1 hd0 hδ hr hm hc
    apply hh.trans
    have hn : (Fintype.card (neighbors G u) : ℝ) ≤ n := by
      exact_mod_cast (show Fintype.card (neighbors G u) ≤ n by
        simpa using (neighbors G u).card_le_univ)
    change 4*((8001 : ℝ)*(n : ℝ)^(-c)+(8000 : ℝ)^8001*2^8000*
      ((Fintype.card (neighbors G u) : ℝ)/D^4000+1/D))^(1/(8000 : ℝ))+7*(n : ℝ)^(-c) ≤ _
    unfold prefixSpectralError
    gcongr
  have hsplit : D⁻¹ • globalLinkAdjacency G hG-globalStarAverage G =
      ∑ u, extendStar (edgeStar G u) (N u) := by
    simp only [globalLinkAdjacency,globalStarAverage,Finset.smul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    have he : N u = D⁻¹ • linkStarMatrix G hG u-averagingProjector := by
      ext i j
      simp only [N,M,linkStarMatrix,Matrix.reindex_apply,Matrix.submatrix_apply,
        Matrix.sub_apply,Matrix.smul_apply,averagingProjector]
      rw [Fintype.card_congr (neighborEdgeEquiv G hG u)]
    rw [he]
    simp [extendStar,Matrix.mul_sub,Matrix.sub_mul,Matrix.smul_mul,Matrix.mul_smul]
  rw [hsplit]
  exact graph_star_error_norm G hG N (fun u => (Matrix.isHermitian_reindex_iff _).mpr (hM u))
    (prefixSpectralError n c) (prefixSpectralError_nonneg n c (zero_le_one.trans hDmin)) hlocal

theorem prefix_degree_wheel_tracking : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    ∀ i ≤ prefixTime n,
    historyAlive (fun j => densityEdgeSafe n (earlyDensity n j) (prefixEdgeRadius n)) (prefixTime n) i ω →
    (∀ u : Fin n, |(currentDegree (ω (historyIndex (prefixTime n) i)) u : ℝ)/
      ((n : ℝ)*earlyDensity n i)-1| ≤ prefixWheelRadius n/2) ∧
    (∀ j, 3 ≤ j → j ≤ 8000 → ∀ u : Fin n,
      |linkCycleCount j (ω (historyIndex (prefixTime n) i)) u/
        ((n : ℝ)*earlyDensity n i^2)^j-1| ≤ prefixWheelRadius n/2) := by
  filter_upwards [prefix_balanced_tracking 8001] with n hn
  intro ω hω hu hnse i hi hs
  have hG : ω (historyIndex (prefixTime n) i) ⊆ completeGraph n := complete_history_valid ω hω i hi
  constructor
  · intro u
    have h := hn ω hω hu hnse i hi hs 2 (by decide) degreeTemplate degreeTemplate_balanced (degreeRoot u)
    rwa [degree_rootedCount _ hG,degree_rootedScaling] at h
  · intro j hj hj' u
    have h := hn ω hω hu hnse i hi hs (j+1) (by omega)
      (wheelTemplate j hj) (wheelTemplate_balanced j hj) (wheelRoot hj u)
    rwa [wheel_rootedCount hj _ hG,wheel_rootedScaling] at h

end SharpTerminalLeave
end
end

end OAI
