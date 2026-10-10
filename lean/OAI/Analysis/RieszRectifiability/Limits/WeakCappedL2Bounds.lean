import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.FiniteWeakProducts
import OAI.Analysis.RieszRectifiability.Kernel.CappedBilinearL2

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem capped_bilinear_integral_tendsto {d : ℕ} (m : ℕ)
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε) (f g : Ambient d →ᵇ ℝ) :
    Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      g q.1 * f q.2 * scalarCappedRieszKernel m e ε q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q
        ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))) := by
  let B := ‖e‖ * (ε ^ m)⁻¹
  let K : Ambient d × Ambient d →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨scalarCappedRieszKernel m e ε, scalarCappedRieszKernel_continuous m e ε hε⟩ (2 * B) (by
      intro q z
      change dist (scalarCappedRieszKernel m e ε q) (scalarCappedRieszKernel m e ε z) ≤ 2 * B
      rw [Real.dist_eq]
      have ht := abs_sub_le (scalarCappedRieszKernel m e ε q) 0 (scalarCappedRieszKernel m e ε z)
      simp only [sub_zero, zero_sub, abs_neg] at ht
      have hq := scalarCappedRieszKernel_bound m e ε hε q
      have hz := scalarCappedRieszKernel_bound m e ε hε z
      dsimp only [B]
      linarith)
  let F : Ambient d × Ambient d →ᵇ ℝ :=
    (g.compContinuous ⟨Prod.fst, continuous_fst⟩ * f.compContinuous ⟨Prod.snd, continuous_snd⟩) * K
  exact finiteMeasure_bounded_product_integral_tendsto μ μ ν ν hweak hweak hν hν F

theorem weak_capped_bilinear_bound_of_native_L2 {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (hgrowth : ∀ j, GlobalUpperGrowth m C (μ j : Measure (Ambient d)))
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j : Measure (Ambient d)) →
      MemLp (truncated m (μ j : Measure (Ambient d)) ε f) 2 (μ j : Measure (Ambient d)) ∧
        eLpNorm (truncated m (μ j : Measure (Ambient d)) ε f) 2 (μ j : Measure (Ambient d)) ≤
          (D : ℝ≥0∞) * eLpNorm f 2 (μ j : Measure (Ambient d)))
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε) (f g : Ambient d →ᵇ ℝ) :
    |∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q
      ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))| ≤
      (‖e‖ * ((D : ℝ) + C * 2 ^ m)) * Real.sqrt (∫ x, g x ^ 2 ∂(ν : Measure (Ambient d))) *
        Real.sqrt (∫ x, f x ^ 2 ∂(ν : Measure (Ambient d))) := by
  have hpair := capped_bilinear_integral_tendsto m μ ν hweak hν e ε hε f g
  have hf : Tendsto (fun j => ∫ x, f x ^ 2 ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, f x ^ 2 ∂(ν : Measure (Ambient d)))) := by
    simpa only [BoundedContinuousFunction.mul_apply, ← pow_two] using!
      FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (f * f)
  have hg : Tendsto (fun j => ∫ x, g x ^ 2 ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, g x ^ 2 ∂(ν : Measure (Ambient d)))) := by
    simpa only [BoundedContinuousFunction.mul_apply, ← pow_two] using!
      FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (g * g)
  have hnorms := (hg.sqrt.const_mul (‖e‖ * ((D : ℝ) + C * 2 ^ m))).mul hf.sqrt
  apply le_of_tendsto_of_tendsto hpair.abs hnorms
  apply Filter.Eventually.of_forall
  intro j
  have hf₂ : MemLp f 2 (μ j : Measure (Ambient d)) :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖ (Filter.Eventually.of_forall f.norm_coe_le_norm)
  have hg₂ : MemLp g 2 (μ j : Measure (Ambient d)) :=
    MemLp.of_bound g.continuous.aestronglyMeasurable ‖g‖ (Filter.Eventually.of_forall g.norm_coe_le_norm)
  obtain ⟨hT, hN⟩ := hB j ε hε f hf₂
  exact capped_bilinear_bound_of_native_L2 m hm C (μ j : Measure (Ambient d)) (hgrowth j)
    D ε hε e f g f.continuous.measurable g.continuous.measurable hf₂ hg₂ hT hN

end

end RieszRectifiability

end OAI
