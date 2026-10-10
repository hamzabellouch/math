import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.StepPairings
import OAI.Analysis.RieszRectifiability.Kernel.PartitionSecondMoments

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem partition_signed_moment_tendsto
    (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set X)
    (hs : ∀ k i, MeasurableSet (s k i))
    (hd : ∀ k, Pairwise (Disjoint on s k))
    (w : ℕ → X → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j))
    (B : ℝ) (hB : ∀ j, (∫ x, w j x ^ 2 ∂μ j) ≤ B)
    (b c : ∀ k, ι k → ℝ)
    (hb : ∀ k i, Tendsto (fun j => cellMean ((μ j).restrict (s k i)) (w j))
      atTop (𝓝 (b k i)))
    (hm : ∀ k i, Tendsto (fun j => (μ j).real (s k i)) atTop (𝓝 (ν.real (s k i))))
    (hpos : ∀ k, ∀ᶠ j in atTop, ∀ i, (μ j).real (s k i) ≠ 0)
    (limit : Lp ℝ 2 ν)
    (hlimit : Tendsto (fun k => (finiteStep_memLp ν (s k) (hs k) (b k)).toLp
      (finiteStep (s k) (b k))) atTop (𝓝 limit))
    (ψ : X → ℝ) (hψ : MemLp ψ 2 ν) (hψj : ∀ j, MemLp ψ 2 (μ j))
    (htest : Tendsto (fun k => (finiteStep_memLp ν (s k) (hs k) (c k)).toLp
      (finiteStep (s k) (c k))) atTop (𝓝 (hψ.toLp ψ)))
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (herr : ∀ k, ∀ᶠ j in atTop,
      (∫ x, (ψ x - finiteStep (s k) (c k) x) ^ 2 ∂μ j) ≤ η k) :
    Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop
      (𝓝 (∫ x, limit x * ψ x ∂ν)) := by
  have hpair : Tendsto (fun k => ∫ x, finiteStep (s k) (b k) x *
      finiteStep (s k) (c k) x ∂ν) atTop (𝓝 (∫ x, limit x * ψ x ∂ν)) := by
    have hl : inner ℝ limit (hψ.toLp ψ) = ∫ x, limit x * ψ x ∂ν := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hψ.coeFn_toLp] with x hx
      rw [hx, real_scalar_inner_mul]
    have hinner := hlimit.inner (𝕜 := ℝ) htest
    simpa only [toLp_inner_eq_integral, hl] using! hinner
  apply tendsto_of_squared_approximation _
    (fun j k => ∫ x, w j x * finiteStep (s k) (c k) x ∂μ j)
    (fun k => ∫ x, finiteStep (s k) (b k) x * finiteStep (s k) (c k) x ∂ν)
    (fun k => B * η k) _ hpair
    (by simpa only [mul_zero] using! hη.const_mul B)
    (fun k => cellMean_step_pairing_tendsto μ ν (s k) (hs k) (hd k) w hw
      (b k) (c k) (hb k) (hm k) (hpos k))
  intro k
  filter_upwards [herr k] with j hj
  have htestNonneg : 0 ≤ ∫ x, (ψ x - finiteStep (s k) (c k) x) ^ 2 ∂μ j :=
    integral_nonneg fun x => sq_nonneg _
  have hworkNonneg : 0 ≤ ∫ x, w j x ^ 2 ∂μ j := integral_nonneg fun x => sq_nonneg _
  have hcs := integral_pairing_difference_sq_le (μ j) ψ (finiteStep (s k) (c k)) (w j)
    (hψj j) (finiteStep_memLp (μ j) (s k) (hs k) (c k)) (hw j)
  have hbound := hcs.trans (mul_le_mul hj (hB j) hworkNonneg (htestNonneg.trans hj))
  simpa only [mul_comm] using! hbound

end

end RieszRectifiability

end OAI
