import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingUniformL2

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

namespace Invariant233.ProductSampling

theorem exists_uniform_energy_bound_of_eventually {e : ℕ → ℝ} {C : ℝ}
    (he : ∀ n, 0 ≤ e n) (hC : ∀ᶠ n in atTop, e n ≤ C) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ n, e n ≤ H := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  let S : ℝ := ∑ n ∈ Finset.range N, e n
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n _ => he n)
  refine ⟨max C S, hS.trans (le_max_right _ _), fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_max_left _ _)
  · exact (Finset.single_le_sum (fun i _ => he i)
      (Finset.mem_range.mpr (by omega))).trans (le_max_right C S)

theorem exists_parameterwise_uniform_energy_bound
    {Ω : Type*} (e : Ω → ℕ → ℝ) (he : ∀ a n, 0 ≤ e a n)
    (hC : ∀ a, ∃ C : ℝ, ∀ᶠ n in atTop, e a n ≤ C) :
    ∃ H : Ω → ℝ, ∀ a, 0 ≤ H a ∧ ∀ n, e a n ≤ H a := by
  classical
  have h : ∀ a, ∃ H : ℝ, 0 ≤ H ∧ ∀ n, e a n ≤ H := by
    intro a
    obtain ⟨C, hC⟩ := hC a
    exact exists_uniform_energy_bound_of_eventually (he a) hC
  choose H hH using h
  exact ⟨H, hH⟩

end Invariant233.ProductSampling

namespace Invariant233.ProductModel

theorem hasUniformL2Marginals_of_eventual_energy_convergence
    (η : ℕ → Measure EndpointPair) (f g z w : ℕ → Base → ℝ)
    (hf : ∀ n, MemLp (f n) 2 baseMeasure)
    (hg : ∀ n, MemLp (g n) 2 baseMeasure)
    (hz : ∀ n, MemLp (z n) 2 baseMeasure)
    (hw : ∀ n, MemLp (w n) 2 baseMeasure)
    (hfnn : ∀ n, ∀ᵐ x ∂baseMeasure, 0 ≤ f n x)
    (hgnn : ∀ n, ∀ᵐ x ∂baseMeasure, 0 ≤ g n x)
    (hfirst : ∀ n, (η n).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (f n x)))
    (hsecond : ∀ n, (η n).map Prod.snd =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (g n x)))
    {C D : ℝ}
    (hzbound : ∀ᶠ n in atTop, (∫ x, (z n x) ^ 2 ∂baseMeasure) ≤ C)
    (hwbound : ∀ᶠ n in atTop, (∫ x, (w n x) ^ 2 ∂baseMeasure) ≤ D)
    (herrf : Tendsto (fun n => ∫ x, (f n x - z n x) ^ 2 ∂baseMeasure)
      atTop (𝓝 0))
    (herrg : Tendsto (fun n => ∫ x, (g n x - w n x) ^ 2 ∂baseMeasure)
      atTop (𝓝 0)) : HasUniformL2Marginals η := by
  obtain ⟨C', _, hC'⟩ := ProductSampling.exists_uniform_energy_bound_of_eventually
    (fun n => integral_nonneg (fun x => sq_nonneg (z n x))) hzbound
  obtain ⟨D', _, hD'⟩ := ProductSampling.exists_uniform_energy_bound_of_eventually
    (fun n => integral_nonneg (fun x => sq_nonneg (w n x))) hwbound
  exact hasUniformL2Marginals_of_energy_convergence η f g z w hf hg hz hw
    hfnn hgnn hfirst hsecond hC' hD' herrf herrg

end Invariant233.ProductModel

end

end OAI
