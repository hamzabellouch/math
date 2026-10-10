import OAI.Algebra.DepthFive.ActualProductRank
import OAI.Algebra.DepthFive.CircuitWeightBound
import OAI.Algebra.DepthFive.CircuitOutputDegree
import OAI.Algebra.DepthFive.ActualWeightParameters
import OAI.Algebra.DepthFive.ConfiguredRankData

namespace OAI

/-! The circuit rank bound for the actual rounded parameters. -/
noncomputable section

namespace Problem335.LowerParameters

/-- The full quantitative circuit estimate with actual source degrees and
dimension. The weight-parameter premise is discharged uniformly eventually. -/
theorem actual_circuit_rank_bound_of_weightParameters
    {K : Type*} [Field K] {n : ℕ} (c : Depth5Circuit K n)
    (side : (Fin n × Fin n × Fin n) → Bool)
    (hvcard : Fintype.card {x // side x = true} = v n)
    (hucard : Fintype.card {x // side x = false} = u n)
    (hp : WeightParameters n (s n) (q n))
    (hc : circuitValue c = imm K n) :
    (bidegreeRank side (a n) (b n) (k n) (m n) (circuitValue c) : ℝ) ≤
      2 * (circuitSize c : ℝ) ^ 2 * sourceDimension n *
        Real.exp ((24 + 4 * Real.log 5) * Real.sqrt n) *
          (n : ℝ) ^ (-Real.sqrt n / 100) := by
  have hn4 : 4 ≤ n := by have := hp.large; omega
  have hnpos : 0 < n := by omega
  let R := fun p : MvPolynomial (Fin n × Fin n × Fin n) K =>
    (bidegreeRank side (a n) (b n) (k n) (m n) p : ℝ)
  have hprod : HomogeneousProductRankBound R n (q n) (lambda n)
      (sourceDimension n) := by
    exact actual_homogeneousProductRankBound hn4 side hvcard hucard
  have hzero : R 0 = 0 := by simp [R]
  have hadd : ∀ p r, R (p + r) ≤ R p + R r := by
    intro p r
    dsimp [R]
    exact_mod_cast bidegreeRank_add_le side (a n) (b n) (k n) (m n) p r
  have hscale : ∀ z p, R (MvPolynomial.C z * p) ≤ R p := by
    intro z p
    dsimp [R, bidegreeRank]
    rw [MvPolynomial.C_mul']
    exact_mod_cast RankMeasure.measure_smul_le
      (bidegreeOperatorFamily side (a n) (b n) (k n) (m n)) z p
  exact circuit_rank_bound_from_product_rank c R hzero hadd hscale
    (s n) (q n) (sourceDimension n) hp (sourceDimension_pos hn4).le
    (outputDegree_eq_of_circuitValue_eq_imm hnpos c hc)
    (by simpa only [lambda_eq_half_sub hnpos] using hprod)

/-- The actual, fixed rank measure satisfies the circuit upper bound after
one absolute threshold. No numerical, product-rank, or partition hypotheses
remain. This is the upper estimate used in the final rank sandwich. -/
theorem exists_rankData_circuit_upper_cutoff :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ c : Depth5Circuit ℂ n,
      circuitValue c = imm ℂ n →
      rankData n (circuitValue c) ≤
        2 * (circuitSize c : ℝ) ^ 2 * rankDimension n *
          Real.exp ((24 + 4 * Real.log 5) * Real.sqrt n) *
            (n : ℝ) ^ (-Real.sqrt n / 100) := by
  obtain ⟨n₀, hn₀⟩ := exists_weightParameters_cutoff
  refine ⟨n₀, fun n hn c hc => ?_⟩
  have hp := hn₀ n hn
  have hn4 : 4 ≤ n := by have := hp.large; omega
  rw [rankData_eq hn4]
  exact actual_circuit_rank_bound_of_weightParameters c
    (fun x : Fin n × Fin n × Fin n => balancedLayer hn4 x.1)
    (balancedVariable_card_true hn4) (balancedVariable_card_false hn4) hp hc

/-- Filter form of the concrete circuit endpoint. -/
theorem eventually_rankData_circuit_upper :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ c : Depth5Circuit ℂ n,
      circuitValue c = imm ℂ n →
      rankData n (circuitValue c) ≤
        2 * (circuitSize c : ℝ) ^ 2 * rankDimension n *
          Real.exp ((24 + 4 * Real.log 5) * Real.sqrt n) *
            (n : ℝ) ^ (-Real.sqrt n / 100) :=
  Filter.eventually_atTop.mpr exists_rankData_circuit_upper_cutoff

end Problem335.LowerParameters

end

end OAI
