import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseRayFactorBounds
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorTrajectoryIncrements
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TrajectoryProductLimits

namespace OAI

/-! # Common compact limits for centered coarse rays -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set Filter
open scoped Manifold Topology Pointwise

/-- The actual factor bounds and compact-set contraction give a common
compact limit set for every ray in a centered coarse family. -/
theorem centered_coarse_ray_quotient_limits
    {P S N D G E Q J : Type*} [MetricSpace S] [One S]
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
    (f : P → S → G) (hcenter : ∀ p, f p 1 = 1)
    {L error R gap B rate : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hgap : 0 < gap) (hB : 0 ≤ B) (hrate : 0 < rate)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ p x,
      |targetHeight (f p x) - sourceHeight x| ≤ ε * dist 1 x + C)
    (ray : ℕ → S) {step : ℝ} (hray : ∀ n, dist 1 (ray n) ≤ R * n)
    (hnegative : ∀ n, sourceHeight (ray n) ≤ -gap * n)
    (hstep : ∀ n, dist (ray n) (ray (n + 1)) ≤ step)
    (degree p : ℕ)
    (hfactor : ∀ g : G, ∃ u d, ι u * κ d = g ∧ 0 ≤ size d ∧
      size d ≤ B * (3 + dist 1 g) ^ degree ∧ height d = targetHeight g)
    (horbit : ∀ r : ℝ, ∃ K : Set Q, IsCompact K ∧ ∀ g, dist 1 g ≤ r → act g 1 ∈ K)
    (hcontract : ∀ K : Set Q, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
      ∀ d, height d ≤ 0 → ∀ q ∈ K,
        ‖b.equivFun (chart.symm (α d q))‖ ≤ A * (1 + size d) ^ p * Real.exp (rate * height d)) :
    ∃ (g : P → Q) (K : Set Q), IsCompact K ∧ (∀ x, g x ∈ K) ∧
      ∀ x, Tendsto (fun n => act (f x (ray n)) 1) atTop (𝓝 (g x)) := by
  let _ : IsTopologicalGroup Q := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨n₀, C, hC, u, d, hlifts, hsteps⟩ := centered_coarse_ray_factor_bounds
    ι κ size height sourceHeight targetHeight f hcenter hL hR hgap hB hf hsub
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
  obtain ⟨g, K', hK', hgK', hg, _⟩ := trajectory_compact_uniform_limit_of_log_increments
    dynkin Exp hExp chart hchart hnil b (fun x n => act (y x n) 1) X a ha hX hXstep
  obtain ⟨K₀, hK₀, hK₀cover⟩ := horbit (L * (R * n₀) + error)
  have hy0 (x : P) : act (y x 0) 1 ∈ K₀ := by
    apply hK₀cover
    have hh := hf x 1 (ray n₀)
    rw [hcenter] at hh
    change dist 1 (f x (ray (0 + n₀))) ≤ _
    rw [zero_add]
    exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left (hray n₀) hL) le_rfl)
  refine ⟨fun x => act (y x 0) 1 * g x, K₀ * K', hK₀.mul hK', ?_, ?_⟩
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
