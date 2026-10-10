import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoundedCoarseRayFactorBounds
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorTrajectoryIncrements
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TrajectoryProductLimits

namespace OAI

/-! # Continuous limits for coarse families with bounded initial points -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set Filter
open scoped Manifold Topology Pointwise

/-- The common logarithmic increment estimate gives a continuous limit for
each continuous coarse family whose initial points are uniformly bounded. -/
theorem continuous_bounded_coarse_ray_quotient_limits
    {P S N D G E Q J : Type*} [TopologicalSpace P] [MetricSpace S] [One S]
    [Group N] [Group D] [Group G] [MetricSpace G] [IsIsometricSMul G G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
    [LieGroup (𝓘(ℝ, E)) ⊤ Q] [T2Space Q] [Fintype J]
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (ι u * κ d) q = π u * α d q)
    (dynkin : NilpotentDynkinExpansionInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) Q ≃ₜ Q) (hchart : ∀ v, chart v = Exp v)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) Q))
    (size height : D → ℝ) (sourceHeight : S → ℝ) (targetHeight : G → ℝ)
    (f : P → S → G) {start : ℝ} (hstart : ∀ p, dist 1 (f p 1) ≤ start)
    {L error R gap B rate : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hgap : 0 < gap) (hB : 0 ≤ B) (hrate : 0 < rate)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ p x,
      |targetHeight (f p x) - sourceHeight x| ≤ ε * dist 1 x + C)
    (ray : ℕ → S) {step : ℝ} (hray : ∀ n, dist 1 (ray n) ≤ R * n)
    (hnegative : ∀ n, sourceHeight (ray n) ≤ -gap * n)
    (hstep : ∀ n, dist (ray n) (ray (n + 1)) ≤ step)
    (hcontinuous : ∀ n, Continuous (fun x => act (f x (ray n)) 1))
    (degree p : ℕ)
    (hfactor : ∀ g : G, ∃ u d, ι u * κ d = g ∧ 0 ≤ size d ∧
      size d ≤ B * (3 + dist 1 g) ^ degree ∧ height d = targetHeight g)
    (horbit : ∀ r : ℝ, ∃ K : Set Q, IsCompact K ∧ ∀ g, dist 1 g ≤ r → act g 1 ∈ K)
    (hcontract : ∀ K : Set Q, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
      ∀ d, height d ≤ 0 → ∀ q ∈ K,
        ‖b.equivFun (chart.symm (α d q))‖ ≤ A * (1 + size d) ^ p * Real.exp (rate * height d)) :
    ∃ (g : P → Q) (K : Set Q), IsCompact K ∧ Continuous g ∧ (∀ x, g x ∈ K) ∧
      ∀ x, Tendsto (fun n => act (f x (ray n)) 1) atTop (𝓝 (g x)) := by
  let _ : IsTopologicalGroup Q := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨n₀, C, hC, u, d, hlifts, hsteps⟩ := bounded_coarse_ray_factor_bounds
    ι κ size height sourceHeight targetHeight f hstart hL hR hgap hB hf hsub
    ray hray hnegative hstep degree hfactor
  let y := fun x n => f x (ray (n + n₀))
  obtain ⟨K, hK, hKcover⟩ := horbit (L * step + error)
  obtain ⟨A, hA, hAc⟩ := hcontract K hK
  have hinc (x : P) (n : ℕ) : act ((y x n)⁻¹ * y x (n + 1)) 1 ∈ K := by
    apply hKcover
    have hd : dist 1 ((y x n)⁻¹ * y x (n + 1)) = dist (y x n) (y x (n + 1)) := by
      simpa only [mul_one, mul_inv_cancel_left] using
        (dist_mul_left (y x n) (1 : G) ((y x n)⁻¹ * y x (n + 1))).symm
    rw [hd]
    exact hsteps x n
  obtain ⟨X, a, ha, hX, hXstep⟩ := factor_trajectory_summable_log_increments
    ι κ π α act hact Exp chart hchart b size height K hA hrate hC (half_pos hgap)
    p degree hAc y u d (fun x n => (hlifts x n).1) (fun x n => (hlifts x n).2.1)
    (fun x n => (hlifts x n).2.2.1) (fun x n => (hlifts x n).2.2.2) hinc
  obtain ⟨g, K', hK', hgK', hg, hu⟩ := trajectory_compact_uniform_limit_of_log_increments
    dynkin Exp hExp chart hchart hnil b (fun x n => act (y x n) 1) X a ha hX hXstep
  obtain ⟨K₀, hK₀, hK₀cover⟩ := horbit (start + L * (R * n₀) + error)
  have hy0 (x : P) : act (y x 0) 1 ∈ K₀ := by
    apply hK₀cover
    have hh := hf x 1 (ray n₀)
    have ht := dist_triangle (1 : G) (f x 1) (f x (ray n₀))
    have hb := hstart x
    have hr := mul_le_mul_of_nonneg_left (hray n₀) hL
    change dist 1 (f x (ray (0 + n₀))) ≤ _
    rw [zero_add]
    linarith
  have hcoords : Continuous (fun z : Q => b.equivFun (chart.symm z)) :=
    b.equivFun.toContinuousLinearEquiv.continuous.comp chart.symm.continuous
  have hnormalized (n : ℕ) : Continuous (fun x =>
      b.equivFun (chart.symm ((act (y x 0) 1)⁻¹ * act (y x n) 1))) := by
    exact hcoords.comp ((hcontinuous (0 + n₀)).inv.mul (hcontinuous (n + n₀)))
  have hgcoords : Continuous (fun x => b.equivFun (chart.symm (g x))) :=
    hu.continuous (Filter.Eventually.of_forall hnormalized).frequently
  have hgcont : Continuous g := by
    have hh := chart.continuous.comp
      (b.equivFun.symm.toContinuousLinearEquiv.continuous.comp hgcoords)
    simpa only [Function.comp_def, LinearEquiv.coe_toContinuousLinearEquiv',
      b.equivFun.symm_apply_apply, chart.apply_symm_apply] using hh
  refine ⟨fun x => act (y x 0) 1 * g x, K₀ * K', hK₀.mul hK', (hcontinuous (0 + n₀)).mul hgcont, ?_, ?_⟩
  · intro x
    exact Set.mul_mem_mul (hy0 x) (hgK' x)
  · intro x
    have hc : Tendsto (fun _ : ℕ => act (y x 0) 1) atTop (𝓝 (act (y x 0) 1)) :=
      tendsto_const_nhds
    have ht := hc.mul (hg x)
    have ht' : Tendsto (fun n => act (y x n) 1) atTop
        (𝓝 (act (y x 0) 1 * g x)) := by
      simpa only [mul_inv_cancel_left] using ht
    exact (tendsto_add_atTop_iff_nat n₀).mp ht'

end PolycyclicRecognition

end

end OAI
