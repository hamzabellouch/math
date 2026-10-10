import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.LipschitzMomentConvergence
import OAI.Analysis.RieszRectifiability.Kernel.CountableLocalization

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

theorem exists_common_localized_signed_limits {X : Type*} [MeasurableSpace X] [MetricSpace X]
    (μ : ℕ → ℕ → Measure X) (ν : ℕ → Measure X)
    [∀ H j, IsFiniteMeasure (μ H j)] [∀ H, IsFiniteMeasure (ν H)]
    (ι : ℕ → ℕ → Type*) [∀ H k, Fintype (ι H k)] (s : ∀ H k, ι H k → Set X)
    (hs : ∀ H k i, MeasurableSet (s H k i)) (hd : ∀ H k, Pairwise (Disjoint on s H k))
    (w : ℕ → ℕ → X → ℝ) (hw : ∀ H j, MemLp (w H j) 2 (μ H j))
    (B : ℕ → ℝ) (hB : ∀ H j, (∫ x, w H j x ^ 2 ∂μ H j) ≤ B H)
    (hm : ∀ H k i, Tendsto (fun j => (μ H j).real (s H k i)) atTop
      (𝓝 ((ν H).real (s H k i))))
    (hmpos : ∀ H k i, 0 < (ν H).real (s H k i))
    (hinter : ∀ H k l i t, Tendsto (fun j => (μ H j).real (s H k i ∩ s H l t)) atTop
      (𝓝 ((ν H).real (s H k i ∩ s H l t))))
    (δ : ℕ → ℕ → ℝ) (hδ : ∀ H, Tendsto (δ H) atTop (𝓝 0))
    (happrox : ∀ H k, ∀ᶠ j in atTop,
      (∫ x, (w H j x - partitionMean (μ H j) (s H k) (w H j) x) ^ 2 ∂μ H j) ≤ δ H k)
    (hcover : ∀ H k j, ∀ᵐ x ∂μ H j, x ∈ ⋃ i, s H k i)
    (hcoverν : ∀ H k, ∀ᵐ x ∂ν H, x ∈ ⋃ i, s H k i)
    (z : ∀ H k, ι H k → X) (r : ℕ → ℕ → ℝ) (hr : ∀ H k, 0 ≤ r H k)
    (hrzero : ∀ H, Tendsto (r H) atTop (𝓝 0)) (M : ℕ → ℝ)
    (htotal : ∀ H, ∀ᶠ j in atTop, (μ H j).real univ ≤ M H)
    (hcell : ∀ H k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ x ∂(μ H j).restrict (s H k i),
      dist x (z H k i) ≤ r H k)
    (hcellν : ∀ H k i, ∀ᵐ x ∂(ν H).restrict (s H k i), dist x (z H k i) ≤ r H k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ∀ H, Lp ℝ 2 (ν H),
      (∀ H, Tendsto (fun j => ∫ x, w H (φ j) x ^ 2 ∂μ H (φ j)) atTop (𝓝 (‖v H‖ ^ 2))) ∧
      ∀ H (ψ : X → ℝ) (L : ℝ≥0), LipschitzWith L ψ → MemLp ψ 2 (ν H) →
        (∀ j, MemLp ψ 2 (μ H (φ j))) →
        Tendsto (fun j => ∫ x, w H (φ j) x * ψ x ∂μ H (φ j)) atTop
          (𝓝 (∫ x, v H x * ψ x ∂ν H)) := by
  obtain ⟨φ, hφ, b, hb, v, hv, hsecond⟩ := exists_common_localized_L2_limits
    μ ν ι s hs hd w hw B hB hm hmpos hinter δ hδ happrox
  refine ⟨φ, hφ, v, hsecond, ?_⟩
  intro H ψ L hLip hψ hψj
  have hpos : ∀ k, ∀ᶠ j in atTop, ∀ i, (μ H (φ j)).real (s H k i) ≠ 0 := by
    intro k
    rw [Filter.eventually_all]
    intro i
    exact (((hm H k i).comp hφ.tendsto_atTop).eventually
      (lt_mem_nhds (hmpos H k i))).mono (fun _ hj => hj.ne')
  exact lipschitz_partition_signed_moment_tendsto (fun j => μ H (φ j)) (ν H)
    (ι H) (s H) (hs H) (hd H) (fun k j => hcover H k (φ j)) (hcoverν H)
    (fun j => w H (φ j)) (fun j => hw H (φ j)) (B H) (fun j => hB H (φ j))
    (b H) (hb H) (fun k i => (hm H k i).comp hφ.tendsto_atTop) hpos (v H) (hv H)
    (z H) (r H) (hr H) (hrzero H) (M H) (hφ.tendsto_atTop.eventually (htotal H))
    (fun k => hφ.tendsto_atTop.eventually (hcell H k)) (hcellν H) ψ L hLip hψ hψj

end

end RieszRectifiability

end OAI
