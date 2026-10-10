import OAI.Algebra.DepthFive.ProductRank
import OAI.Algebra.DepthFive.OperatorRankBridge

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ K ι : Type*} [Fintype σ] [Field K] [Fintype ι] [DecidableEq ι]

/-- The product-rank estimate in the common rank API used by both circuit
and moment bounds. Its dimension factor is the actual source dimension. -/
theorem bidegreeRank_product_le_degreeWeight
    (side : σ → Bool) (Q : ι → MvPolynomial σ K) (e : ι → ℕ)
    (hQ : ∀ j, (Q j).IsHomogeneous (e j))
    (k m v u a b : ℕ) (rho lam : ℝ)
    (hvcard : Fintype.card {x : σ // side x = true} = v)
    (hucard : Fintype.card {x : σ // side x = false} = u)
    (he : ∑ j, e j = k + m) (hproportion : lam * (k + m) = k)
    (hslope : (1 + rho) * lam = rho)
    (hv : 1 ≤ v) (hu : 1 ≤ u) (ha : 0 < a) (hb : 0 < b)
    (hka : k ≤ a) (hbudget : 2 * k ≤ a + v)
    (hbalance : ((a : ℝ) / ((a : ℝ) + v)) ^ rho ≤
      (b : ℝ) / ((b : ℝ) + u)) :
    (bidegreeRank side a b k m (∏ j, Q j) : ℝ) ≤
      2 * (Module.finrank K (bidegreeSubmodule (K := K) side a b) : ℝ) *
        ∏ j, degreeWeight (((a : ℝ) / ((a : ℝ) + v)) ^ ((1 + rho) / 2)) lam (e j) := by
  have h := mixed_product_rank_le side Q e hQ k (k + m) v u a b rho lam
    hvcard hucard he (by simpa only [Nat.cast_add] using hproportion) hslope hv hu ha hb hka hbudget hbalance
  rw [bidegreeRank_eq_source_measure]
  rw [bidegreeSubmodule_finrank_choose K side, hvcard, hucard, Nat.cast_mul]
  simpa only [Nat.add_sub_cancel_left, RankMeasure.measure, homogeneousDim] using h

end Problem335

end

end OAI
