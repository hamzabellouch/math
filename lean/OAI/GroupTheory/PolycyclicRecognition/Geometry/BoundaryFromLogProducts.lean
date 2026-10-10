import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformDynkinProducts

namespace OAI

/-!
# Boundary limits from contracting logarithmic increments

The actual finite BCH estimate constructs uniform normalized limits in
a common compact set. Continuous trajectories then define a continuous
boundary map on an actual quotient whenever trajectories in a common
fiber are asymptotic. Only that geometric fiber condition remains an
input here; no boundary map or compact shadow is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter Metric
open scoped BigOperators Manifold Topology

variable {E G J P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [Fintype J]

/-- The normalized product limits of a whole contracting family lie in
one compact set, while convergence is uniform in exponential coordinates. -/
theorem exists_compact_uniform_log_product_limit
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C : ℝ} (hC : 0 ≤ C) (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (X : P → ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (d : ℕ → ℝ) (hd : Summable d)
    (hX : ∀ p n, ‖b.equivFun (X p n)‖ ≤ d n) :
    ∃ (g : P → G) (K : Set G), IsCompact K ∧ (∀ p, g p ∈ K) ∧
      (∀ p, Tendsto (exponentialPartialProduct Exp (X p)) atTop (𝓝 (g p))) ∧
      TendstoUniformly
        (fun n p => b.equivFun (chart.symm (exponentialPartialProduct Exp (X p) n)))
        (fun p => b.equivFun (chart.symm (g p))) atTop := by
  obtain ⟨g, hg, hu⟩ := exists_uniform_limit_of_summable_log_products
    dynkin Exp hExp chart hchart hc b hC hbracket X d hd hX
  let R := (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
    (∑' k, d k) * (1 + ∑' k, d k) ^ c
  let k : (J → ℝ) → G := fun v => chart (b.equivFun.symm v)
  have hk : Continuous k := chart.continuous.comp b.equivFun.symm.toContinuousLinearEquiv.continuous
  have hcoords : Continuous (fun q : G => b.equivFun (chart.symm q)) :=
    b.equivFun.toContinuousLinearEquiv.continuous.comp chart.symm.continuous
  have hbound (p : P) (n : ℕ) :
      ‖b.equivFun (chart.symm (exponentialPartialProduct Exp (X p) n))‖ ≤ R := by
    obtain ⟨z, hz, hzbound⟩ := exists_tail_product_log_bound
      dynkin Exp hExp hc b hC hbracket (X p) d hd (hX p) 0 n
    have hz' : exponentialPartialProduct Exp (X p) n = Exp z := by
      simpa only [zero_add] using hz
    rw [hz', ← hchart, chart.symm_apply_apply]
    simpa only [zero_add, R] using hzbound
  refine ⟨g, k '' closedBall 0 R, (isCompact_closedBall (0 : J → ℝ) R).image hk, ?_, hg, hu⟩
  intro p
  have hlim := (hcoords.norm.tendsto (g p)).comp (hg p)
  have hnorm : ‖b.equivFun (chart.symm (g p))‖ ≤ R :=
    le_of_tendsto hlim (Filter.Eventually.of_forall (hbound p))
  refine ⟨b.equivFun (chart.symm (g p)), ?_, ?_⟩
  · simpa only [mem_closedBall, dist_zero_right] using hnorm
  · simp only [k, b.equivFun.symm_apply_apply, chart.apply_symm_apply]

/-- Contracting logarithmic increments and geometric asymptotic equality
on fibers construct the continuous boundary map and a fixed compact
normalized shadow. -/
theorem exists_quotient_boundary_of_summable_log_increments
    {Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    (q : P → Q) (hq : Topology.IsQuotientMap q)
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C : ℝ} (hC : 0 ≤ C) (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (X : P → ℕ → GroupLieAlgebra (𝓘(ℝ, E)) G) (d : ℕ → ℝ) (hd : Summable d)
    (hX : ∀ p n, ‖b.equivFun (X p n)‖ ≤ d n)
    (f : P → ℕ → G) (hcontinuous : ∀ n, Continuous (fun p => f p n))
    (hstep : ∀ p n, f p (n + 1) = f p n * Exp (X p n))
    (hfiber : ∀ p p', q p = q p' →
      Tendsto (fun n => (f p n)⁻¹ * f p' n) atTop (𝓝 (1 : G))) :
    ∃ (B : Q → G) (K : Set G), Continuous B ∧ IsCompact K ∧
      (∀ p, Tendsto (f p) atTop (𝓝 (B (q p)))) ∧
      ∀ p, ∃ k ∈ K, B (q p) = f p 0 * k := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨g, K, hK, hgK, hg, hu⟩ := exists_compact_uniform_log_product_limit
    dynkin Exp hExp chart hchart hc b hC hbracket X d hd hX
  have hfactor (p : P) (n : ℕ) : f p n = f p 0 * exponentialPartialProduct Exp (X p) n := by
    induction n with
    | zero => simp [exponentialPartialProduct]
    | succ n ih =>
      rw [hstep, ih, exponentialPartialProduct_add Exp (X p) n 1]
      simp [exponentialPartialProduct, mul_assoc]
  have hnorm (p : P) (n : ℕ) : exponentialPartialProduct Exp (X p) n = (f p 0)⁻¹ * f p n := by
    rw [hfactor p n]
    simp
  have hcoords : Continuous (fun g : G => b.equivFun (chart.symm g)) :=
    b.equivFun.toContinuousLinearEquiv.continuous.comp chart.symm.continuous
  have hnormcont (n : ℕ) : Continuous
      (fun p => b.equivFun (chart.symm (exponentialPartialProduct Exp (X p) n))) := by
    simp_rw [hnorm]
    exact hcoords.comp ((hcontinuous 0).inv.mul (hcontinuous n))
  have hgcoords : Continuous (fun p => b.equivFun (chart.symm (g p))) :=
    hu.continuous (Filter.Eventually.of_forall hnormcont).frequently
  have hgcont : Continuous g := by
    have hh := chart.continuous.comp
      (b.equivFun.symm.toContinuousLinearEquiv.continuous.comp hgcoords)
    simpa only [Function.comp_def, LinearEquiv.coe_toContinuousLinearEquiv',
      b.equivFun.symm_apply_apply, chart.apply_symm_apply] using hh
  let B₀ : P → G := fun p => f p 0 * g p
  have hB₀ : Continuous B₀ := (hcontinuous 0).mul hgcont
  have hlim (p : P) : Tendsto (f p) atTop (𝓝 (B₀ p)) := by
    have hh : Tendsto (fun n => f p 0 * exponentialPartialProduct Exp (X p) n)
        atTop (𝓝 (f p 0 * g p)) := tendsto_const_nhds.mul (hg p)
    simpa only [← hfactor p] using hh
  have heq (p p' : P) (hp : q p = q p') : B₀ p = B₀ p' := by
    have hh := tendsto_nhds_unique ((hlim p).inv.mul (hlim p')) (hfiber p p' hp)
    exact inv_mul_eq_one.mp hh
  choose s hs using hq.surjective
  let B : Q → G := fun y => B₀ (s y)
  have hdesc (p : P) : B (q p) = B₀ p := heq _ _ (hs (q p))
  refine ⟨B, K, hq.continuous_iff.mpr ?_, hK, ?_, ?_⟩
  · simpa only [Function.comp_def, hdesc] using hB₀
  · intro p
    rw [hdesc]
    exact hlim p
  · intro p
    exact ⟨g p, hgK p, hdesc p⟩

end PolycyclicRecognition

end

end OAI
