import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinSummableProducts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryLimits
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Sequences

namespace OAI

/-!
# Convergence of products with summable logarithmic increments

Finite BCH gives a common bound on every tail product in terms of the
sum of its logarithmic increments. The global exponential chart then
gives convergence, without identifying its coordinate metric with a
left invariant metric.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter Metric
open scoped BigOperators Manifold Topology

variable {E G J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [Fintype J]

/-- The ordered product of the first `m` exponential increments. -/
def exponentialPartialProduct
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (X : ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (m : ℕ) : G :=
  (List.ofFn (fun i : Fin m => Exp (X i))).prod

omit [FiniteDimensional ℝ E] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] in
theorem exponentialPartialProduct_add
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (X : ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (n m : ℕ) :
    exponentialPartialProduct Exp X (n + m) =
      exponentialPartialProduct Exp X n *
        exponentialPartialProduct Exp (fun k => X (n + k)) m := by
  simp only [exponentialPartialProduct, List.ofFn_add, List.prod_append]
  congr 2

/-- Summability controls the logarithm of every finite tail product,
uniformly in the number of tail factors. -/
theorem exists_tail_product_log_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C : ℝ} (hC : 0 ≤ C) (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (X : ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (d : ℕ → ℝ) (hd : Summable d)
    (hX : ∀ n, ‖b.equivFun (X n)‖ ≤ d n) (n m : ℕ) :
    ∃ z, exponentialPartialProduct Exp (fun k => X (n + k)) m = Exp z ∧
      ‖b.equivFun z‖ ≤
        (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
          (∑' k, d (n + k)) * (1 + ∑' k, d (n + k)) ^ c := by
  obtain ⟨z, hz, hb⟩ := exists_product_log_with_sum_bound dynkin Exp hExp hc b hC hbracket
    (fun i : Fin m => X (n + i))
  have hnonneg (k : ℕ) : 0 ≤ d k := (norm_nonneg _).trans (hX k)
  have hsum : (∑ i : Fin m, ‖b.equivFun (X (n + i))‖) ≤ ∑' k, d (n + k) := by
    calc
      _ ≤ ∑ i : Fin m, d (n + i) := Finset.sum_le_sum (fun i _ => hX (n + i))
      _ = ∑ k ∈ Finset.range m, d (n + k) :=
        Fin.sum_univ_eq_sum_range (fun k => d (n + k)) m
      _ ≤ _ := Summable.sum_le_tsum _ (fun k _ => hnonneg (n + k))
        (hd.comp_injective (fun a b h => Nat.add_left_cancel h))
  refine ⟨z, hz, hb.trans ?_⟩
  have hsum0 : 0 ≤ ∑ i : Fin m, ‖b.equivFun (X (n + i))‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have ht0 : 0 ≤ ∑' k, d (n + k) := tsum_nonneg (fun k => hnonneg (n + k))
  gcongr

/-- The common bound for all finite tail products tends to zero. -/
theorem dynkin_tail_bound_tendsto_zero
    (A : ℝ) (c : ℕ) (d : ℕ → ℝ) :
    Tendsto (fun n => A * (∑' k, d (n + k)) * (1 + ∑' k, d (n + k)) ^ c)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => ∑' k, d (n + k)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using tendsto_sum_nat_add d
  simpa using (tendsto_const_nhds.mul ht).mul ((tendsto_const_nhds.add ht).pow c)

/-- Actual ordered products with summable logarithmic increments converge
in the global exponential chart. The proof uses the common finite-tail
bound and compactness in coordinates, not a metric invariance assumption. -/
theorem exponentialPartialProduct_tendsto_of_summable
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C : ℝ} (hC : 0 ≤ C) (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (X : ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (d : ℕ → ℝ) (hd : Summable d)
    (hX : ∀ n, ‖b.equivFun (X n)‖ ≤ d n) :
    ∃ g : G, Tendsto (exponentialPartialProduct Exp X) atTop (𝓝 g) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let A := (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c
  let B := fun n => A * (∑' k, d (n + k)) * (1 + ∑' k, d (n + k)) ^ c
  have htail (n m : ℕ) : ∃ z,
      exponentialPartialProduct Exp (fun k => X (n + k)) m = Exp z ∧
        ‖b.equivFun z‖ ≤ B n :=
    exists_tail_product_log_bound dynkin Exp hExp hc b hC hbracket X d hd hX n m
  have hB : Tendsto B atTop (𝓝 0) := dynkin_tail_bound_tendsto_zero A c d
  choose z hz hzb using fun m => htail 0 m
  have hz' (m : ℕ) : exponentialPartialProduct Exp X m = Exp (z m) := by
    simpa only [zero_add] using hz m
  have hbounded (m : ℕ) : b.equivFun (z m) ∈ closedBall 0 (B 0) := by
    simpa only [mem_closedBall, dist_zero_right] using hzb m
  obtain ⟨a, _, r, hr, hconv⟩ := (isCompact_closedBall (0 : J → ℝ) (B 0)).tendsto_subseq hbounded
  let g := Exp (b.equivFun.symm a)
  have hExpcont : Continuous Exp := by
    have heq : (chart : GroupLieAlgebra (𝓘(ℝ, E)) G → G) = Exp := funext hchart
    rw [← heq]
    exact chart.continuous
  have hsubseq : Tendsto (fun n => exponentialPartialProduct Exp X (r n)) atTop (𝓝 g) := by
    have ht := (hExpcont.comp b.equivFun.symm.toContinuousLinearEquiv.continuous).tendsto a |>.comp hconv
    simpa only [Function.comp_def, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.symm_apply_apply, g, ← hz'] using ht
  choose w hw hwb using fun n => htail n (r n - n)
  have hwzero : Tendsto (fun n => b.equivFun (w n)) atTop (𝓝 0) :=
    squeeze_zero_norm hwb hB
  have hwExp : Tendsto (fun n => Exp (w n)) atTop (𝓝 (1 : G)) := by
    have ht := (hExpcont.comp b.equivFun.symm.toContinuousLinearEquiv.continuous).tendsto 0 |>.comp hwzero
    simpa only [Function.comp_def, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.symm_apply_apply, map_zero, hExp.map_zero] using ht
  have hidentity (n : ℕ) : exponentialPartialProduct Exp X n =
      exponentialPartialProduct Exp X (r n) * (Exp (w n))⁻¹ := by
    apply eq_mul_inv_iff_mul_eq.mpr
    have hh := exponentialPartialProduct_add Exp X n (r n - n)
    have hn : n ≤ r n := hr.id_le n
    rw [Nat.add_sub_of_le hn, hw n] at hh
    exact hh.symm
  refine ⟨g, ?_⟩
  have ht := hsubseq.mul hwExp.inv
  simpa only [inv_one, mul_one, ← hidentity] using ht

/-- The same conclusion for an actual trajectory specified by its
successive exponential increments. -/
theorem trajectory_tendsto_of_summable_log_increments
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C : ℝ} (hC : 0 ≤ C) (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (X : ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (d : ℕ → ℝ) (hd : Summable d)
    (hX : ∀ n, ‖b.equivFun (X n)‖ ≤ d n)
    (f : ℕ → G) (hstep : ∀ n, f (n + 1) = f n * Exp (X n)) :
    ∃ g : G, Tendsto f atTop (𝓝 g) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨g, hg⟩ := exponentialPartialProduct_tendsto_of_summable
    dynkin Exp hExp chart hchart hc b hC hbracket X d hd hX
  have hf (n : ℕ) : f n = f 0 * exponentialPartialProduct Exp X n := by
    induction n with
    | zero => simp [exponentialPartialProduct]
    | succ n ih =>
      rw [hstep, ih, exponentialPartialProduct_add Exp X n 1]
      simp [exponentialPartialProduct, mul_assoc]
  refine ⟨f 0 * g, ?_⟩
  have ht : Tendsto (fun n => f 0 * exponentialPartialProduct Exp X n) atTop
      (𝓝 (f 0 * g)) := tendsto_const_nhds.mul hg
  simpa only [← hf] using ht

/-- Finite chains whose total logarithmic increment size tends to zero
have endpoint product tending to the identity, even if their lengths grow. -/
theorem finite_exp_products_tendsto_one
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hcontinuous : Continuous Exp)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C : ℝ} (hC : 0 ≤ C) (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (m : ℕ → ℕ) (X : (n : ℕ) → Fin (m n) → GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hsmall : Tendsto (fun n => ∑ i, ‖b.equivFun (X n i)‖) atTop (𝓝 0)) :
    Tendsto (fun n => (List.ofFn (fun i => Exp (X n i))).prod) atTop (𝓝 (1 : G)) := by
  let A := (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c
  choose z hz hbound using fun n =>
    exists_product_log_with_sum_bound dynkin Exp hExp hc b hC hbracket (X n)
  have hlim : Tendsto
      (fun n => A * (∑ i, ‖b.equivFun (X n i)‖) * (1 + ∑ i, ‖b.equivFun (X n i)‖) ^ c)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hsmall).mul ((tendsto_const_nhds.add hsmall).pow c)
  have hzsmall : Tendsto (fun n => b.equivFun (z n)) atTop (𝓝 0) :=
    squeeze_zero_norm hbound hlim
  have ht := (hcontinuous.comp b.equivFun.symm.toContinuousLinearEquiv.continuous).tendsto 0 |>.comp hzsmall
  simpa only [Function.comp_def, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearEquiv.symm_apply_apply, map_zero,
    hExp.map_zero, ← hz] using ht

omit [FiniteDimensional ℝ E] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] in
/-- Polynomially many exponentially small increments have vanishing total
size. This is the endpoint estimate for the representative-independence
paths in `boundary.tex`. -/
theorem sum_norm_tendsto_zero_of_polynomial_count_exp_steps
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (m : ℕ → ℕ) (X : (n : ℕ) → Fin (m n) → GroupLieAlgebra (𝓘(ℝ, E)) G)
    (A K c : ℝ) (p q : ℕ) (hA : 0 ≤ A) (hc : 0 < c)
    (hcount : ∀ n, (m n : ℝ) ≤ K * (1 + (n : ℝ)) ^ q)
    (hstep : ∀ n i, ‖b.equivFun (X n i)‖ ≤
      A * (1 + (n : ℝ)) ^ p * Real.exp (-c * n)) :
    Tendsto (fun n => ∑ i, ‖b.equivFun (X n i)‖) atTop (𝓝 0) := by
  have hbound (n : ℕ) : (∑ i, ‖b.equivFun (X n i)‖) ≤
      (K * A) * (1 + (n : ℝ)) ^ (p + q) * Real.exp (-c * n) := by
    calc
      _ ≤ ∑ _i : Fin (m n), A * (1 + (n : ℝ)) ^ p * Real.exp (-c * n) :=
        Finset.sum_le_sum (fun i _ => hstep n i)
      _ = (m n : ℝ) * (A * (1 + (n : ℝ)) ^ p * Real.exp (-c * n)) := by simp
      _ ≤ (K * (1 + (n : ℝ)) ^ q) *
          (A * (1 + (n : ℝ)) ^ p * Real.exp (-c * n)) := by
        apply mul_le_mul_of_nonneg_right (hcount n)
        positivity
      _ = _ := by rw [pow_add]; ring
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n =>
    Finset.sum_nonneg (fun i _ => norm_nonneg _))) (Filter.Eventually.of_forall hbound)
  exact (summable_polynomial_exp_decay (K * A) (p + q) hc).tendsto_atTop_zero

end PolycyclicRecognition

end

end OAI
