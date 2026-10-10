import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.PartitionCompactness

namespace OAI

/-!
# Second moments from partition approximations

Convergence of partition masses and coefficients gives convergence of finite-step L²
norms. Vanishing squared approximation errors then transfer this convergence to the
second moments of the original functions under varying measures.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

theorem tendsto_of_squared_approximation (u : ℕ → ℝ) (p : ℕ → ℕ → ℝ)
    (v δ : ℕ → ℝ) (L : ℝ) (hv : Tendsto v atTop (𝓝 L))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hp : ∀ k, Tendsto (fun j => p j k) atTop (𝓝 (v k)))
    (herr : ∀ k, ∀ᶠ j in atTop, (u j - p j k) ^ 2 ≤ δ k) :
    Tendsto u atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have hsmall := hδ.eventually (gt_mem_nhds (show (0 : ℝ) < (ε / 3) ^ 2 by positivity))
  obtain ⟨k, hkδ, hkv⟩ := (hsmall.and (Metric.tendsto_nhds.mp hv _ hthird)).exists
  filter_upwards [herr k, Metric.tendsto_nhds.mp (hp k) _ hthird] with j hj hjp
  have hdist : dist (u j) (p j k) < ε / 3 := by
    rw [Real.dist_eq]
    nlinarith [sq_abs (u j - p j k), abs_nonneg (u j - p j k)]
  calc
    dist (u j) L ≤ dist (u j) (p j k) + dist (p j k) L := dist_triangle _ _ _
    _ ≤ dist (u j) (p j k) + (dist (p j k) (v k) + dist (v k) L) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ < ε := by linarith

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

theorem finiteStep_L2_norm_tendsto (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (a : ℕ → ι → ℝ) (b : ι → ℝ)
    (ha : ∀ i, Tendsto (fun j => a j i) atTop (𝓝 (b i)))
    (hm : ∀ i, Tendsto (fun j => (μ j).real (s i)) atTop (𝓝 (ν.real (s i)))) :
    Tendsto (fun j => ‖(finiteStep_memLp (μ j) s hs (a j)).toLp (finiteStep s (a j))‖)
      atTop (𝓝 ‖(finiteStep_memLp ν s hs b).toLp (finiteStep s b)‖) := by
  have hsq : Tendsto
      (fun j => ‖(finiteStep_memLp (μ j) s hs (a j)).toLp (finiteStep s (a j))‖ ^ 2)
      atTop (𝓝 (‖(finiteStep_memLp ν s hs b).toLp (finiteStep s b)‖ ^ 2)) := by
    simp_rw [toLp_norm_sq_eq_integral, integral_finiteStep_sq _ s hs hd]
    exact tendsto_finsetSum _ fun i _ => (hm i).mul ((ha i).pow 2)
  simpa only [Real.sqrt_sq (norm_nonneg _)] using! hsq.sqrt

theorem toLp_norm_difference_sq_le (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (‖hf.toLp f‖ - ‖hg.toLp g‖) ^ 2 ≤ ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [← toLp_dist_sq_eq_integral μ f g hf hg, dist_eq_norm]
  have h := (sq_le_sq₀ (abs_nonneg (‖hf.toLp f‖ - ‖hg.toLp g‖))
    (norm_nonneg (hf.toLp f - hg.toLp g))).mpr (abs_norm_sub_norm_le _ _)
  simpa only [sq_abs] using! h

theorem partition_approximation_second_moments_tendsto
    (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set X)
    (hs : ∀ k i, MeasurableSet (s k i))
    (hd : ∀ k, Pairwise (Disjoint on s k))
    (w : ℕ → X → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j))
    (a : ℕ → ∀ k, ι k → ℝ) (b : ∀ k, ι k → ℝ)
    (ha : ∀ k i, Tendsto (fun j => a j k i) atTop (𝓝 (b k i)))
    (hm : ∀ k i, Tendsto (fun j => (μ j).real (s k i)) atTop (𝓝 (ν.real (s k i))))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (happrox : ∀ k, ∀ᶠ j in atTop,
      (∫ x, (w j x - finiteStep (s k) (a j k) x) ^ 2 ∂μ j) ≤ δ k)
    (limit : Lp ℝ 2 ν)
    (hlimit : Tendsto (fun k => (finiteStep_memLp ν (s k) (hs k) (b k)).toLp
      (finiteStep (s k) (b k))) atTop (𝓝 limit)) :
    Tendsto (fun j => ∫ x, w j x ^ 2 ∂μ j) atTop (𝓝 (‖limit‖ ^ 2)) := by
  have hnorm : Tendsto (fun j => ‖(hw j).toLp (w j)‖) atTop (𝓝 ‖limit‖) := by
    apply tendsto_of_squared_approximation _
      (fun j k => ‖(finiteStep_memLp (μ j) (s k) (hs k) (a j k)).toLp
        (finiteStep (s k) (a j k))‖)
      (fun k => ‖(finiteStep_memLp ν (s k) (hs k) (b k)).toLp
        (finiteStep (s k) (b k))‖) δ ‖limit‖ hlimit.norm hδ
      (fun k => finiteStep_L2_norm_tendsto μ ν (s k) (hs k) (hd k)
        (fun j => a j k) (b k) (ha k) (hm k))
    intro k
    filter_upwards [happrox k] with j hj
    exact (toLp_norm_difference_sq_le (μ j) (w j) (finiteStep (s k) (a j k))
      (hw j) (finiteStep_memLp (μ j) (s k) (hs k) (a j k))).trans hj
  simpa only [toLp_norm_sq_eq_integral] using! hnorm.pow 2

end

end RieszRectifiability

end OAI
