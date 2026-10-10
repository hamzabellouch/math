import OAI.Algebra.DepthFive.ProductRankAssembly
import OAI.Algebra.DepthFive.IntermediateFactorization
import OAI.Algebra.DepthFive.IntermediateDimension
import OAI.Algebra.DepthFive.BidegreeDimension
import OAI.Algebra.DepthFive.BidegreeBridge

namespace OAI

/-! The mixed-operator product-rank estimate.  Unlike the abstract assembly
lemma, the intermediate-space rank bounds here are proved from the actual
operator, and its dimension is computed from the two variable groups. -/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ K ι : Type*} [Fintype σ] [Field K] [Fintype ι] [DecidableEq ι]

/-- The product-rank lemma for a homogeneous product, under the elementary
numerical hypotheses on the source degrees and balancing ratios.
There is no circuit or polynomial rank hypothesis in this statement. -/
theorem mixed_product_rank_le
    (side : σ → Bool) (Q : ι → MvPolynomial σ K) (e : ι → ℕ)
    (hQ : ∀ j, (Q j).IsHomogeneous (e j))
    (k n v u a b : ℕ) (rho lam : ℝ)
    (hvcard : Fintype.card {x : σ // side x = true} = v)
    (hucard : Fintype.card {x : σ // side x = false} = u)
    (he : ∑ j, e j = n) (hproportion : lam * n = k)
    (hslope : (1 + rho) * lam = rho)
    (hv : 1 ≤ v) (hu : 1 ≤ u) (ha : 0 < a) (hb : 0 < b)
    (hka : k ≤ a) (hbudget : 2 * k ≤ a + v)
    (hbalance : ((a : ℝ) / ((a : ℝ) + v)) ^ rho ≤
      (b : ℝ) / ((b : ℝ) + u)) :
    (RankMeasure.mapRank (sourceMixedOperator side a b
      (bidegreeComponent side k (n - k) (∏ j, Q j))) : ℝ) ≤
      2 * ((homogeneousDim v a : ℝ) * homogeneousDim u b) *
        ∏ j, degreeWeight (((a : ℝ) / ((a : ℝ) + v)) ^ ((1 + rho) / 2)) lam (e j) := by
  classical
  have htotal : (∏ j, Q j).IsHomogeneous n := by
    rw [← he]
    exact MvPolynomial.IsHomogeneous.prod _ _ _ (fun j _ => hQ j)
  rw [bidegreeComponent_sub_eq_component side k htotal]
  change (RankMeasure.measure (sourceMixedOperator side a b)
    (Bidegree.component side k (∏ j, Q j)) : ℝ) ≤ _
  refine ProductRankAssembly.measure_component_product_le_degreeWeight
    (fun p => (RankMeasure.measure (sourceMixedOperator side a b) p : ℝ))
    (by simp) ?_ side Q e hQ k
    (2 * ((homogeneousDim v a : ℝ) * homogeneousDim u b))
    (((a : ℝ) / ((a : ℝ) + v)) ^ ((1 + rho) / 2)) lam
    (by positivity) (by positivity) ?_
  · intro p q
    exact_mod_cast RankMeasure.measure_add_le (sourceMixedOperator side a b) p q
  · intro i hie hi
    have hIa : positiveBidegreeV Finset.univ e i lam ≤ a := by
      calc
        _ ≤ ∑ j, i j := positiveBidegreeV_le Finset.univ e i lam
        _ = k := hi
        _ ≤ a := hka
    have hrank := sourceMixedOperator_homogeneous_prod_rank_le Finset.univ
      (fun j => 0 < (i j : ℝ) - lam * e j)
      (fun j => Bidegree.component side (i j) (Q j))
      i (fun j => e j - i j) side a b
      (fun j _ => component_mem_bidegreeSubmodule side (i j) (hQ j)) hIa
    rw [bidegreeSubmodule_finrank_choose K side, hvcard, hucard] at hrank
    have hrankR :
        (RankMeasure.measure (sourceMixedOperator side a b)
          (∏ j, Bidegree.component side (i j) (Q j)) : ℝ) ≤
        (homogeneousDim v (a - positiveBidegreeV Finset.univ e i lam) : ℝ) *
          homogeneousDim u (b + positiveBidegreeU Finset.univ e i lam) := by
      exact_mod_cast hrank
    exact hrankR.trans (intermediate_dimension_le_weight_product Finset.univ
      e i k n v u a b rho lam (fun j _ => hie j) he hi
      hproportion hslope hv hu ha hb hka hbudget hbalance)

end Problem335

end

end OAI
