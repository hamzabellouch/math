import OAI.Probability.FreeIsing.Ising.CopyEdgeVariance
import OAI.Probability.FreeIsing.Ising.CopyPathVector
import OAI.Probability.FreeIsing.Trees.ColoredPathCoefficients
import OAI.Probability.FreeIsing.Trees.PathPrefix

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor
open ColoredEdgeLifts ColoredPathAverage ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem inner_rooted_cavityLogVector_eq_of_length_eq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (a b : TreeVertex d) (hlen : a.1.length = b.1.length) (n : ℕ) :
    inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex a 1))
      (cavityLogVector hμ hbeta t (takeVertex a n) a) =
    inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex b 1))
      (cavityLogVector hμ hbeta t (takeVertex b n) b) := by
  obtain ⟨g, hga, hgroot⟩ := exists_rootFixing_treeAut_map a b hlen
  have hgroot' : g.toEquiv (root d) = root d := hgroot
  have hfirst := g.map_takeVertex_of_root_eq hgroot' a 1
  have hlast := g.map_takeVertex_of_root_eq hgroot' a n
  rw [hga] at hfirst hlast
  have h := inner_cavityLogVector_map hμ hbeta g t (root d) (takeVertex a 1)
    (takeVertex a n) a
  rw [hgroot', hfirst, hlast, hga] at h
  exact h.symm

theorem inner_pathValue_eq_rooted_cavityLogVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {n : ℕ} {i : Fin d} (p : Path d n i)
    (v : TreeVertex d) (hlen : v.1.length = n + 1) :
    inner ℝ (cavityLogEdgeVector hμ hbeta t i)
      (pathValue (differenceReflection hμ) (cavityLogEdgeVector hμ hbeta t) p) =
    inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex v 1))
      (cavityLogVector hμ hbeta t (takeVertex v n) v) := by
  rw [pathValue_cavityLogEdgeVector]
  change inner ℝ (cavityLogVector hμ hbeta t (root d) (prefixFlip i TreeEscape.root))
    (cavityLogVector hμ hbeta t (tailVertex p) (headVertex p)) = _
  have hfirst : takeVertex (headVertex p) 1 = prefixFlip i TreeEscape.root := by
    cases n <;> apply Subtype.ext <;> rfl
  have htail : tailVertex p = takeVertex (headVertex p) n := by
    apply Subtype.ext
    change (colors p).dropLast = (colors p).take n
    rw [List.dropLast_eq_take, colors_length]
    simp
  rw [← hfirst, htail]
  apply inner_rooted_cavityLogVector_eq_of_length_eq hμ hbeta t _ v _ n
  simpa only [headVertex, colors_length] using hlen.symm

theorem inner_forwardOperator_eq_rooted_cavityLogVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 2 ≤ d) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (n : ℕ) (v : TreeVertex d) (hlen : v.1.length = n + 1) :
    inner ℝ (cavityLogEdgeVector hμ hbeta t)
      ((forwardOperator (by omega : 0 < d) (differenceReflection hμ)
        ((d : ℝ) - 1)⁻¹ ^ n) (cavityLogEdgeVector hμ hbeta t)) =
      (d : ℝ) * inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex v 1))
        (cavityLogVector hμ hbeta t (takeVertex v n) v) := by
  apply inner_forwardOperator_pow_eq_card_mul hd
  intro i p
  exact inner_pathValue_eq_rooted_cavityLogVector hμ hbeta t p v hlen

theorem abs_inner_rooted_cavityLogVector_le_norm_pow
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 2 ≤ d) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (n : ℕ) (v : TreeVertex d) (hlen : v.1.length = n + 1)
    {u w : TreeVertex d} (huw : treeAdj u w) :
    |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex v 1))
      (cavityLogVector hμ hbeta t (takeVertex v n) v)| ≤
      ‖forwardOperator (by omega : 0 < d) (differenceReflection hμ)
        ((d : ℝ) - 1)⁻¹ ^ n‖ *
        ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ := by
  apply abs_pathCoefficient_le_norm_pow hd (differenceReflection hμ) n
    (cavityLogEdgeVector hμ hbeta t)
  · intro i p
    exact inner_pathValue_eq_rooted_cavityLogVector hμ hbeta t p v hlen
  · exact (norm_cavityLogEdgeVector_sq_eq hμ hbeta t huw).le

theorem exists_rooted_cavityLogVector_correlation_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ≥0) (n : ℕ) (v : TreeVertex d),
      v.1.length = n + 1 → ∀ (u w : TreeVertex d), treeAdj u w →
      |inner ℝ (cavityLogVector hμ hbeta t (root d) (takeVertex v 1))
        (cavityLogVector hμ hbeta t (takeVertex v n) v)| ≤
        (K * ((n : ℝ) + 1) * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n) *
          ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ := by
  obtain ⟨K, hK, hpow⟩ := forwardOperator_pow_bound hμ hd hbeta hthreshold
  refine ⟨K, hK, ?_⟩
  intro t n v hlen u w huw
  exact (abs_inner_rooted_cavityLogVector_le_norm_pow hμ (by omega) hbeta t n v
    hlen huw).trans (mul_le_mul_of_nonneg_right (hpow n)
      (integral_nonneg (fun q => sq_nonneg _)))

theorem exists_rooted_cavityLogDifference_pair_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ≥0) (n : ℕ) (v : TreeVertex d),
      v.1.length = n + 1 → ∀ (u w : TreeVertex d), treeAdj u w →
      |∫ q, cavityLogDifference hbeta t (root d) (takeVertex v 1) q *
        cavityLogDifference hbeta t (takeVertex v n) v q ∂copies beta μ| ≤
        (K * ((n : ℝ) + 1) * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n) *
          ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ := by
  obtain ⟨K, hK, h⟩ := exists_rooted_cavityLogVector_correlation_bound hμ hd hbeta hthreshold
  refine ⟨K, hK, ?_⟩
  intro t n v hlen u w huw
  simpa only [inner_cavityLogVector_eq_integral] using h t n v hlen u w huw

end Problem367.IsingCopySpectral

end

end OAI
