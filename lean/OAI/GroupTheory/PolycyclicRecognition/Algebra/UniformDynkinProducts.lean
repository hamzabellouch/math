import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinProductTails
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-!
# Uniform convergence in exponential coordinates

Compact coordinate balls give a uniform modulus for right multiplication
by a small exponential. Combining it with the common BCH tail estimate
gives uniform convergence of families of contracting products. No
invariance of the coordinate metric is asserted or used.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter Metric
open scoped BigOperators Manifold Topology

/-- Right multiplication by a point tending to the identity approaches the
identity map uniformly on each bounded coordinate ball. -/
theorem exists_coordinate_mul_modulus
    {V G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (e : V ≃ₜ G) (he : e 0 = 1) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : V, ‖x‖ ≤ R → ∀ y : V, ‖y‖ < δ →
      dist (e.symm (e x * e y)) x < ε := by
  let K : Set V := closedBall 0 R
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : V) R)
  let F : V → K → V := fun y x => e.symm (e x.val * e y)
  have hF : Continuous (Function.uncurry F) :=
    e.symm.continuous.comp ((e.continuous.comp continuous_snd.subtype_val).mul
      (e.continuous.comp continuous_fst))
  have hu := Continuous.tendstoUniformly F hF 0
  have hn := (Metric.tendstoUniformly_iff.mp hu) ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy
  let x' : K := ⟨x, by simpa only [K, mem_closedBall, dist_zero_right] using hx⟩
  have hh := hb (show y ∈ ball 0 δ by simpa only [mem_ball, dist_zero_right] using hy) x'
  simpa only [F, he, mul_one, e.symm_apply_apply, dist_comm] using hh

/-- Pointwise limits of a uniformly Cauchy family of sequences are uniform
limits. The tail estimate is only needed in the forward direction. -/
theorem tendstoUniformly_of_uniform_forward_cauchy
    {P V : Type*} [PseudoMetricSpace V] (f : P → ℕ → V) (b : P → V)
    (hlim : ∀ p, Tendsto (f p) atTop (𝓝 (b p)))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p n, N ≤ n → ∀ m, n ≤ m →
      dist (f p n) (f p m) < ε) :
    TendstoUniformly (fun n p => f p n) b atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε / 2) (half_pos hε)
  filter_upwards [eventually_ge_atTop N] with n hn p
  have hh : dist (f p n) (b p) ≤ ε / 2 := by
    apply le_of_tendsto (tendsto_const_nhds.dist (hlim p))
    filter_upwards [eventually_ge_atTop n] with m hm
    exact (hN p n hn m hm).le
  exact (dist_comm _ _).trans_le hh |>.trans_lt (half_lt_self hε)

section ActualProducts

variable {E G J P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [Fintype J]

/-- A common summable logarithmic increment bound gives uniform convergence
in any fixed global exponential coordinates. This applies simultaneously
to the normalized trajectories for an entire quasi-isometry family. -/
theorem exists_uniform_limit_of_summable_log_products
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C : ℝ} (hC : 0 ≤ C) (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (X : P → ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (d : ℕ → ℝ) (hd : Summable d)
    (hX : ∀ p n, ‖b.equivFun (X p n)‖ ≤ d n) :
    ∃ g : P → G,
      (∀ p, Tendsto (exponentialPartialProduct Exp (X p)) atTop (𝓝 (g p))) ∧
      TendstoUniformly
        (fun n p => b.equivFun (chart.symm (exponentialPartialProduct Exp (X p) n)))
        (fun p => b.equivFun (chart.symm (g p))) atTop := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let e : (J → ℝ) ≃ₜ G := b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have he (v : J → ℝ) : e v = Exp (b.equivFun.symm v) := hchart _
  have he0 : e 0 = 1 := by rw [he, map_zero, hExp.map_zero]
  have heExp (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : e.symm (Exp v) = b.equivFun v := by
    have hh : Exp v = e (b.equivFun v) := by rw [he, b.equivFun.symm_apply_apply]
    rw [hh, e.symm_apply_apply]
  have heInv (g : G) : e.symm g = b.equivFun (chart.symm g) := rfl
  let A := (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c
  let B := fun n => A * (∑' k, d (n + k)) * (1 + ∑' k, d (n + k)) ^ c
  have hB : Tendsto B atTop (𝓝 0) := dynkin_tail_bound_tendsto_zero A c d
  have htail (p : P) (n m : ℕ) : ∃ z,
      exponentialPartialProduct Exp (fun k => X p (n + k)) m = Exp z ∧
        ‖b.equivFun z‖ ≤ B n :=
    exists_tail_product_log_bound dynkin Exp hExp hc b hC hbracket (X p) d hd (hX p) n m
  choose g hg using fun p => exponentialPartialProduct_tendsto_of_summable
    dynkin Exp hExp chart hchart hc b hC hbracket (X p) d hd (hX p)
  refine ⟨g, hg, ?_⟩
  have hprefix (p : P) (n : ℕ) : ‖e.symm (exponentialPartialProduct Exp (X p) n)‖ ≤ B 0 := by
    obtain ⟨z, hz, hbound⟩ := htail p 0 n
    have hz' : exponentialPartialProduct Exp (X p) n = Exp z := by simpa only [zero_add] using hz
    rw [hz', heExp]
    exact hbound
  have huniform : TendstoUniformly
      (fun n p => e.symm (exponentialPartialProduct Exp (X p) n)) (fun p => e.symm (g p)) atTop := by
    apply tendstoUniformly_of_uniform_forward_cauchy
    · intro p
      exact e.symm.continuous.tendsto (g p) |>.comp (hg p)
    · intro ε hε
      obtain ⟨δ, hδ, hmul⟩ := exists_coordinate_mul_modulus e he0 (B 0) hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hB.eventually (eventually_lt_nhds hδ))
      refine ⟨N, ?_⟩
      intro p n hn m hnm
      obtain ⟨z, hz, hbound⟩ := htail p n (m - n)
      have hfactor := exponentialPartialProduct_add Exp (X p) n (m - n)
      rw [Nat.add_sub_of_le hnm, hz] at hfactor
      have hh := hmul (e.symm (exponentialPartialProduct Exp (X p) n)) (hprefix p n)
        (b.equivFun z) (hbound.trans_lt (hN n hn))
      rw [e.apply_symm_apply, he, b.equivFun.symm_apply_apply, ← hfactor] at hh
      exact (dist_comm _ _).trans_lt hh
  simpa only [heInv] using huniform

end ActualProducts
end PolycyclicRecognition

end

end OAI
