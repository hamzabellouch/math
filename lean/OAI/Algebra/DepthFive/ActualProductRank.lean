import OAI.Algebra.DepthFive.ProductRankCanonical
import OAI.Algebra.DepthFive.CircuitWeightBound
import OAI.Algebra.DepthFive.AnalyticParameters

namespace OAI

/-! Product-rank estimates specialized to the actual rounded rank parameters. -/
noncomputable section
open scoped BigOperators

namespace Problem335.LowerParameters

/-- Dimension of the source of the actual mixed operator. -/
def sourceDimension (n : ℕ) : ℝ :=
  (homogeneousDim (v n) (a n) : ℝ) * homogeneousDim (u n) (b n)

theorem sourceDimension_pos {n : ℕ} (hn : 4 ≤ n) : 0 < sourceDimension n := by
  unfold sourceDimension
  exact mul_pos (by exact_mod_cast homogeneousDim_pos (v_pos hn) (a n))
    (by exact_mod_cast homogeneousDim_pos (u_pos hn) (b n))

theorem slope_lambda {n : ℕ} (hn : 4 ≤ n) :
    (1 + rho n) * lambda n = rho n := by
  rw [lambda_eq_rho_div hn]
  have h : 1 + rho n ≠ 0 := by have := rho_pos hn; linarith
  exact mul_div_cancel₀ _ h

theorem twice_k_le_a_add_v {n : ℕ} (hn : 4 ≤ n) :
    2 * k n ≤ a n + v n := by
  have h := k_mul_n_le_a hn
  have hmul : 2 * k n ≤ k n * n := by nlinarith
  omega

/-- All numerical hypotheses of the mixed product-rank lemma hold for our
chosen parameters. Only the cardinalities of the variable partition remain. -/
theorem actual_mixed_product_rank_le
    {σ K ι : Type*} [Fintype σ] [Field K] [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 4 ≤ n) (side : σ → Bool)
    (hvcard : Fintype.card {x : σ // side x = true} = v n)
    (hucard : Fintype.card {x : σ // side x = false} = u n)
    (Q : ι → MvPolynomial σ K) (e : ι → ℕ)
    (hQ : ∀ j, (Q j).IsHomogeneous (e j)) (he : ∑ j, e j = n) :
    (RankMeasure.mapRank (sourceMixedOperator side (a n) (b n)
      (bidegreeComponent side (k n) (m n) (∏ j, Q j))) : ℝ) ≤
      2 * sourceDimension n * ∏ j, degreeWeight (q n) (lambda n) (e j) := by
  have hmk : n - k n = m n := by have := k_add_m n; omega
  simpa only [hmk, sourceDimension, q, alpha] using
    mixed_product_rank_le side Q e hQ (k n) n (v n) (u n) (a n) (b n)
      (rho n) (lambda n) hvcard hucard he (lambda_mul_n n) (slope_lambda hn)
      (v_pos hn) (u_pos hn) (a_pos hn) (b_pos hn) (k_le_a hn)
      (twice_k_le_a_add_v hn) (alpha_rpow_rho_le_beta hn)

/-- The dimension factor is exactly the dimension of the chosen source space. -/
theorem sourceDimension_eq_finrank {σ : Type*} [Fintype σ]
    (K : Type*) [Field K] (n : ℕ) (side : σ → Bool)
    (hvcard : Fintype.card {x : σ // side x = true} = v n)
    (hucard : Fintype.card {x : σ // side x = false} = u n) :
    sourceDimension n =
      (Module.finrank K (bidegreeSubmodule (K := K) side (a n) (b n)) : ℝ) := by
  rw [bidegreeSubmodule_finrank_choose K side, hvcard, hucard, Nat.cast_mul]
  rfl

/-- The canonical finite-source rank has the actual-parameter product bound. -/
theorem actual_bidegreeRank_product_le
    {σ K ι : Type*} [Fintype σ] [Field K] [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 4 ≤ n) (side : σ → Bool)
    (hvcard : Fintype.card {x : σ // side x = true} = v n)
    (hucard : Fintype.card {x : σ // side x = false} = u n)
    (Q : ι → MvPolynomial σ K) (e : ι → ℕ)
    (hQ : ∀ j, (Q j).IsHomogeneous (e j)) (he : ∑ j, e j = n) :
    (bidegreeRank side (a n) (b n) (k n) (m n) (∏ j, Q j) : ℝ) ≤
      2 * sourceDimension n * ∏ j, degreeWeight (q n) (lambda n) (e j) := by
  rw [bidegreeRank_eq_source_measure]
  exact actual_mixed_product_rank_le hn side hvcard hucard Q e hQ he

/-- The full list interface consumed by the circuit estimate, with every
analytic and operator-rank hypothesis discharged for the actual parameters. -/
theorem actual_homogeneousProductRankBound
    {σ K : Type*} [Fintype σ] [Field K]
    {n : ℕ} (hn : 4 ≤ n) (side : σ → Bool)
    (hvcard : Fintype.card {x : σ // side x = true} = v n)
    (hucard : Fintype.card {x : σ // side x = false} = u n) :
    HomogeneousProductRankBound
      (fun p : MvPolynomial σ K =>
        (bidegreeRank side (a n) (b n) (k n) (m n) p : ℝ))
      n (q n) (lambda n) (sourceDimension n) := by
  apply homogeneousProductRankBound_of_fin
  intro r P e _hepos hP he
  exact actual_bidegreeRank_product_le hn side hvcard hucard P e hP he

end Problem335.LowerParameters

end

end OAI
