import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.SignedMomentConvergence
import OAI.Analysis.RieszRectifiability.Kernel.TestStepApproximation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

variable {X : Type*} [MeasurableSpace X] [MetricSpace X]

theorem lipschitz_partition_signed_moment_tendsto
    (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set X)
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ x ∂μ j, x ∈ ⋃ i, s k i)
    (hcoverν : ∀ k, ∀ᵐ x ∂ν, x ∈ ⋃ i, s k i)
    (w : ℕ → X → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j))
    (B : ℝ) (hB : ∀ j, (∫ x, w j x ^ 2 ∂μ j) ≤ B)
    (b : ∀ k, ι k → ℝ)
    (hb : ∀ k i, Tendsto (fun j => cellMean ((μ j).restrict (s k i)) (w j))
      atTop (𝓝 (b k i)))
    (hm : ∀ k i, Tendsto (fun j => (μ j).real (s k i)) atTop (𝓝 (ν.real (s k i))))
    (hpos : ∀ k, ∀ᶠ j in atTop, ∀ i, (μ j).real (s k i) ≠ 0)
    (limit : Lp ℝ 2 ν)
    (hlimit : Tendsto (fun k => (finiteStep_memLp ν (s k) (hs k) (b k)).toLp
      (finiteStep (s k) (b k))) atTop (𝓝 limit))
    (z : ∀ k, ι k → X) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0)) (M : ℝ)
    (hmass : ∀ᶠ j in atTop, (μ j).real univ ≤ M)
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ x ∂(μ j).restrict (s k i),
      dist x (z k i) ≤ r k)
    (hcellν : ∀ k i, ∀ᵐ x ∂ν.restrict (s k i), dist x (z k i) ≤ r k)
    (ψ : X → ℝ) (K : ℝ≥0) (hLip : LipschitzWith K ψ)
    (hψ : MemLp ψ 2 ν) (hψj : ∀ j, MemLp ψ 2 (μ j)) :
    Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop
      (𝓝 (∫ x, limit x * ψ x ∂ν)) := by
  let c : ∀ k, ι k → ℝ := fun k i => ψ (z k i)
  have hscale (D : ℝ) : Tendsto (fun k => D * ((K : ℝ) * r k) ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using!
      ((hrzero.const_mul (K : ℝ)).pow 2).const_mul D
  have hνerror : Tendsto (fun k => ∫ x, (ψ x - finiteStep (s k) (c k) x) ^ 2 ∂ν)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => integral_nonneg (fun x => sq_nonneg _))
      (fun k => lipschitz_step_test_error_le ν (s k) (hs k) (hd k) ψ hψ
        K hLip (z k) (r k) (hr k) (hcoverν k) (hcellν k))
      (hscale (ν.real univ))
  have hνerror' : Tendsto (fun k => ∫ x, (finiteStep (s k) (c k) x - ψ x) ^ 2 ∂ν)
      atTop (𝓝 0) := by
    convert! hνerror using 1
    funext k
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by ring)
  have htest := L2_tendsto_of_squared_error ν (fun k => finiteStep (s k) (c k)) ψ
    (fun k => finiteStep_memLp ν (s k) (hs k) (c k)) hψ hνerror'
  apply partition_signed_moment_tendsto μ ν ι s hs hd w hw B hB b c hb hm hpos
    limit hlimit ψ hψ hψj htest (fun k => M * ((K : ℝ) * r k) ^ 2) (hscale M)
  intro k
  filter_upwards [hmass, hcell k] with j hjmass hjcell
  exact (lipschitz_step_test_error_le (μ j) (s k) (hs k) (hd k) ψ (hψj j)
    K hLip (z k) (r k) (hr k) (hcover k j) hjcell).trans
    (mul_le_mul_of_nonneg_right hjmass (sq_nonneg _))

end

end RieszRectifiability

end OAI
