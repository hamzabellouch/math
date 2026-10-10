import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ApproximationComparison

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem exists_L2_limit_of_partition_approximations
    (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set X)
    (hs : ∀ k i, MeasurableSet (s k i))
    (hd : ∀ k, Pairwise (Disjoint on s k))
    (w : ℕ → X → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j))
    (a : ℕ → ∀ k, ι k → ℝ) (b : ∀ k, ι k → ℝ)
    (ha : ∀ k i, Tendsto (fun j => a j k i) atTop (𝓝 (b k i)))
    (hm : ∀ k i, Tendsto (fun j => (μ j).real (s k i)) atTop (𝓝 (ν.real (s k i))))
    (hinter : ∀ k l i t, Tendsto (fun j => (μ j).real (s k i ∩ s l t))
      atTop (𝓝 (ν.real (s k i ∩ s l t))))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (happrox : ∀ k, ∀ᶠ j in atTop,
      (∫ x, (w j x - finiteStep (s k) (a j k) x) ^ 2 ∂μ j) ≤ δ k) :
    ∃ limit : Lp ℝ 2 ν,
      Tendsto (fun k => (finiteStep_memLp ν (s k) (hs k) (b k)).toLp
        (finiteStep (s k) (b k))) atTop (𝓝 limit) := by
  apply exists_L2_limit_of_sq_distance_bound ν _ δ hδ
  intro k l
  rw [toLp_dist_sq_eq_integral]
  apply fixed_pair_bound_of_approximations μ ν (finiteStep (s k) (b k))
    (finiteStep (s l) (b l)) (fun j => finiteStep (s k) (a j k)) w
    (fun j => finiteStep (s l) (a j l))
    (fun j => finiteStep_memLp (μ j) (s k) (hs k) (b k))
    (fun j => finiteStep_memLp (μ j) (s l) (hs l) (b l))
    (fun j => finiteStep_memLp (μ j) (s k) (hs k) (a j k)) hw
    (fun j => finiteStep_memLp (μ j) (s l) (hs l) (a j l))
    (δ k) (δ l) (happrox k) (happrox l)
  · exact finiteStep_squared_error_tendsto_zero μ (s k) (hs k) (hd k)
      (fun j => a j k) (b k) _ (ha k) (hm k)
  · exact finiteStep_squared_error_tendsto_zero μ (s l) (hs l) (hd l)
      (fun j => a j l) (b l) _ (ha l) (hm l)
  · exact finiteStep_cross_distance_tendsto μ ν (s k) (s l) (hs k) (hs l)
      (hd k) (hd l) (b k) (b l) (hm k) (hm l) (hinter k l)

theorem exists_subsequence_partition_L2_limit
    (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set X)
    (hs : ∀ k i, MeasurableSet (s k i))
    (hd : ∀ k, Pairwise (Disjoint on s k))
    (w : ℕ → X → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j))
    (B : ℝ) (hB : ∀ j, (∫ x, w j x ^ 2 ∂μ j) ≤ B)
    (hm : ∀ k i, Tendsto (fun j => (μ j).real (s k i)) atTop (𝓝 (ν.real (s k i))))
    (hmpos : ∀ k i, 0 < ν.real (s k i))
    (hinter : ∀ k l i t, Tendsto (fun j => (μ j).real (s k i ∩ s l t))
      atTop (𝓝 (ν.real (s k i ∩ s l t))))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (happrox : ∀ k, ∀ᶠ j in atTop,
      (∫ x, (w j x - partitionMean (μ j) (s k) (w j) x) ^ 2 ∂μ j) ≤ δ k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ b : ∀ k, ι k → ℝ,
      (∀ k i, Tendsto (fun j => cellMean ((μ (φ j)).restrict (s k i)) (w (φ j)))
        atTop (𝓝 (b k i))) ∧
      ∃ limit : Lp ℝ 2 ν,
        Tendsto (fun k => (finiteStep_memLp ν (s k) (hs k) (b k)).toLp
          (finiteStep (s k) (b k))) atTop (𝓝 limit) := by
  have hlower (p : Σ k, ι k) : ∃ c : ℝ, 0 < c ∧
      ∀ᶠ j in atTop, c ≤ (μ j).real (s p.1 p.2) := by
    refine ⟨ν.real (s p.1 p.2) / 2, half_pos (hmpos p.1 p.2), ?_⟩
    exact ((hm p.1 p.2).eventually
      (lt_mem_nhds (half_lt_self (hmpos p.1 p.2)))).mono (fun _ h => h.le)
  obtain ⟨b, φ, hφ, hcoeff⟩ := exists_subsequence_cellMeans μ w hw
    (fun p : Σ k, ι k => s p.1 p.2) B hB hlower
  refine ⟨φ, hφ, (fun k i => b ⟨k, i⟩), (fun k i => hcoeff ⟨k, i⟩), ?_⟩
  apply exists_L2_limit_of_partition_approximations (fun j => μ (φ j)) ν ι s hs hd
    (fun j => w (φ j)) (fun j => hw (φ j))
    (fun j k i => cellMean ((μ (φ j)).restrict (s k i)) (w (φ j)))
    (fun k i => b ⟨k, i⟩) (fun k i => hcoeff ⟨k, i⟩)
    (fun k i => (hm k i).comp hφ.tendsto_atTop)
    (fun k l i t => (hinter k l i t).comp hφ.tendsto_atTop) δ hδ
  intro k
  simpa only [partitionMean_eq_finiteStep] using! hφ.tendsto_atTop.eventually (happrox k)

end

end RieszRectifiability

end OAI
