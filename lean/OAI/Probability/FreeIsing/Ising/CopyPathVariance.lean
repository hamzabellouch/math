import OAI.Probability.FreeIsing.Ising.CopyFixedPathBound
import OAI.Probability.FreeIsing.Trees.IndexedPathVariance
import OAI.Probability.FreeIsing.Trees.PathRerooting
import OAI.Probability.FreeIsing.Trees.PathReverseRerooting

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor
open ConnectedHull
open scoped NNReal

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

private theorem inner_path_pair_bound_of_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {K q S : ℝ}
    (hroot : ∀ (n : ℕ) (w : TreeVertex d), w.1.length = n + 1 →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex w 1))
        (cavityLogVector hμ hbeta t (takeVertex w n) w)| ≤
          K * ((n : ℝ) + 1) * q ^ n * S)
    (v : TreeVertex d) {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    |inner ℝ (cavityLogVector hμ hbeta t (takeVertex v i) (takeVertex v (i + 1)))
      (cavityLogVector hμ hbeta t (takeVertex v j) (takeVertex v (j + 1)))| ≤
        (K * S) * pathCorrelationKernel q ((j : ℤ) - (i : ℤ)) := by
  obtain ⟨w, g, hlen, hi, hi1, hj0, hj1⟩ :=
    exists_treeAut_reroot_edge_pair v hij hj
  have hm := inner_cavityLogVector_map hμ hbeta g t
    (takeVertex v i) (takeVertex v (i + 1))
    (takeVertex v j) (takeVertex v (j + 1))
  rw [hi, hi1, hj0, hj1] at hm
  rw [← hm]
  have hlag : ((j : ℤ) - (i : ℤ)).natAbs = j - i := by
    rw [← Int.natCast_sub hij]
    rfl
  calc
    _ ≤ K * (((j - i : ℕ) : ℝ) + 1) * q ^ (j - i) * S := hroot _ w hlen
    _ = _ := by rw [pathCorrelationKernel, hlag]; ring

private theorem inner_reverse_path_pair_bound_of_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {K q S : ℝ}
    (hroot : ∀ (n : ℕ) (w : TreeVertex d), w.1.length = n + 1 →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex w 1))
        (cavityLogVector hμ hbeta t (takeVertex w n) w)| ≤
          K * ((n : ℝ) + 1) * q ^ n * S)
    (v : TreeVertex d) {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    |inner ℝ (cavityLogVector hμ hbeta t (takeVertex v (i + 1)) (takeVertex v i))
      (cavityLogVector hμ hbeta t (takeVertex v (j + 1)) (takeVertex v j))| ≤
        (K * S) * pathCorrelationKernel q ((j : ℤ) - (i : ℤ)) := by
  obtain ⟨w, g, hlen, hi, hi1, hj0, hj1⟩ :=
    exists_treeAut_reroot_reverse_edge_pair v hij hj
  have hm := inner_cavityLogVector_map hμ hbeta g t
    (takeVertex v (j + 1)) (takeVertex v j)
    (takeVertex v (i + 1)) (takeVertex v i)
  rw [hi, hi1, hj0, hj1] at hm
  rw [real_inner_comm, ← hm]
  have hlag : ((j : ℤ) - (i : ℤ)).natAbs = j - i := by
    rw [← Int.natCast_sub hij]
    rfl
  calc
    _ ≤ K * (((j - i : ℕ) : ℝ) + 1) * q ^ (j - i) * S := hroot _ w hlen
    _ = _ := by rw [pathCorrelationKernel, hlag]; ring

private theorem integral_image_path_sq_bound_of_root_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {K q S : ℝ} (hK : 0 ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hS : 0 ≤ S)
    (hroot : ∀ (n : ℕ) (w : TreeVertex d), w.1.length = n + 1 →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex w 1))
        (cavityLogVector hμ hbeta t (takeVertex w n) w)| ≤
          K * ((n : ℝ) + 1) * q ^ n * S)
    (g : TreeAut d) (v : TreeVertex d) :
    (∫ ω, (∑ i : Fin v.1.length, cavityLogDifference hbeta t
      (g.toEquiv (takeVertex v i)) (g.toEquiv (takeVertex v (i + 1))) ω) ^ 2
        ∂copies beta μ) ≤
      (K * (2 / (1 - q) ^ 2 - 1)) * (v.1.length : ℝ) * S := by
  have h := integral_sum_fin_sq_le_ordered_geometric_pair_bound
    (fun i => cavityLogDifference hbeta t
      (g.toEquiv (takeVertex v i)) (g.toEquiv (takeVertex v (i + 1))))
    hq0 hq1 (mul_nonneg hK hS)
    (fun i => memLp_cavityLogDifference hμ hbeta t _ _)
    (fun i j hij => by
      rw [← inner_cavityLogVector_eq_integral hμ hbeta t,
        inner_cavityLogVector_map]
      have hpair := inner_path_pair_bound_of_le hμ hbeta t hroot v hij j.isLt
      simpa only [pathCorrelationKernel,
        Int.natAbs_natCast_sub_natCast_of_ge hij, mul_assoc] using hpair)
  calc
    _ ≤ (v.1.length : ℝ) * (K * S) * (2 / (1 - q) ^ 2 - 1) := h
    _ = _ := by ring

private theorem integral_image_reverse_path_sq_bound_of_root_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {K q S : ℝ} (hK : 0 ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hS : 0 ≤ S)
    (hroot : ∀ (n : ℕ) (w : TreeVertex d), w.1.length = n + 1 →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex w 1))
        (cavityLogVector hμ hbeta t (takeVertex w n) w)| ≤
          K * ((n : ℝ) + 1) * q ^ n * S)
    (g : TreeAut d) (v : TreeVertex d) :
    (∫ ω, (∑ i : Fin v.1.length, cavityLogDifference hbeta t
      (g.toEquiv (takeVertex v (i + 1))) (g.toEquiv (takeVertex v i)) ω) ^ 2
        ∂copies beta μ) ≤
      (K * (2 / (1 - q) ^ 2 - 1)) * (v.1.length : ℝ) * S := by
  have h := integral_sum_fin_sq_le_ordered_geometric_pair_bound
    (fun i => cavityLogDifference hbeta t
      (g.toEquiv (takeVertex v (i + 1))) (g.toEquiv (takeVertex v i)))
    hq0 hq1 (mul_nonneg hK hS)
    (fun i => memLp_cavityLogDifference hμ hbeta t _ _)
    (fun i j hij => by
      rw [← inner_cavityLogVector_eq_integral hμ hbeta t,
        inner_cavityLogVector_map]
      have hpair := inner_reverse_path_pair_bound_of_le hμ hbeta t hroot v hij j.isLt
      simpa only [pathCorrelationKernel,
        Int.natAbs_natCast_sub_natCast_of_ge hij, mul_assoc] using hpair)
  calc
    _ ≤ (v.1.length : ℝ) * (K * S) * (2 / (1 - q) ^ 2 - 1) := h
    _ = _ := by ring

theorem exists_cavityLog_path_variance_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w →
      ∀ (g : TreeAut d) (v : TreeVertex d),
      ((∫ ω, (∑ i : Fin v.1.length, cavityLogDifference hbeta t
          (g.toEquiv (takeVertex v i)) (g.toEquiv (takeVertex v (i + 1))) ω) ^ 2
            ∂copies beta μ) ≤
        C * (v.1.length : ℝ) *
          ∫ ω, (cavityLogDifference hbeta t u w ω) ^ 2 ∂copies beta μ) ∧
      ((∫ ω, (∑ i : Fin v.1.length, cavityLogDifference hbeta t
          (g.toEquiv (takeVertex v (i + 1))) (g.toEquiv (takeVertex v i)) ω) ^ 2
            ∂copies beta μ) ≤
        C * (v.1.length : ℝ) *
          ∫ ω, (cavityLogDifference hbeta t u w ω) ^ 2 ∂copies beta μ) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_rooted_cavityLogVector_correlation_bound hμ hd hbeta hthreshold
  let q := (Real.sqrt ((d : ℝ) - 1))⁻¹
  have hq0 : 0 ≤ q := (ColoredEdgeLifts.degree_decay_parameters hd).1.le
  have hq1 : q < 1 := (ColoredEdgeLifts.degree_decay_parameters hd).2.1
  have hmass : 0 ≤ 2 / (1 - q) ^ 2 - 1 := by
    rw [← tsum_pathCorrelationKernel hq0 hq1]
    exact tsum_nonneg (pathCorrelationKernel_nonneg hq0)
  refine ⟨K * (2 / (1 - q) ^ 2 - 1), mul_nonneg hK hmass, ?_⟩
  intro t u w huw g v
  have hS : 0 ≤ ∫ ω, (cavityLogDifference hbeta t u w ω) ^ 2 ∂copies beta μ :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hroot := fun n x hx => hbound t n x hx u w huw
  exact ⟨integral_image_path_sq_bound_of_root_bound hμ hbeta t hK hq0 hq1 hS
      hroot g v,
    integral_image_reverse_path_sq_bound_of_root_bound hμ hbeta t hK hq0 hq1 hS
      hroot g v⟩

end Problem367.IsingCopySpectral

end

end OAI
