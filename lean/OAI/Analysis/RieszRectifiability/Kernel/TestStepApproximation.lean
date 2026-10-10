import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.FiniteStepLp

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

theorem finiteStep_test_error_le (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (ψ : X → ℝ) (hψ : MemLp ψ 2 μ)
    (c : ι → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i)
    (hcell : ∀ i, ∀ᵐ x ∂μ.restrict (s i), |ψ x - c i| ≤ D) :
    (∫ x, (ψ x - finiteStep s c x) ^ 2 ∂μ) ≤ μ.real univ * D ^ 2 := by
  have hc : ∀ᵐ x ∂μ, ∀ i, x ∈ s i → |ψ x - c i| ≤ D :=
    ae_all_iff.mpr (fun i => (ae_restrict_iff' (hs i)).mp (hcell i))
  have hb : ∀ᵐ x ∂μ, (ψ x - finiteStep s c x) ^ 2 ≤ D ^ 2 := by
    filter_upwards [hcover, hc] with x hx hcx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [finiteStep_eq_cell s c hd i x hi]
    simpa only [sq_abs] using! (sq_le_sq₀ (abs_nonneg _) hD).mpr (hcx i hi)
  have h := integral_mono_ae ((hψ.sub (finiteStep_memLp μ s hs c)).integrable_sq)
    (integrable_const (D ^ 2)) hb
  simpa only [integral_const, smul_eq_mul] using! h

variable [MetricSpace X]

theorem lipschitz_step_test_error_le (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (ψ : X → ℝ) (hψ : MemLp ψ 2 μ)
    (K : ℝ≥0) (hLip : LipschitzWith K ψ) (z : ι → X)
    (r : ℝ) (hr : 0 ≤ r) (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i)
    (hcell : ∀ i, ∀ᵐ x ∂μ.restrict (s i), dist x (z i) ≤ r) :
    (∫ x, (ψ x - finiteStep s (fun i => ψ (z i)) x) ^ 2 ∂μ) ≤
      μ.real univ * ((K : ℝ) * r) ^ 2 := by
  apply finiteStep_test_error_le μ s hs hd ψ hψ _ _ (mul_nonneg K.coe_nonneg hr) hcover
  intro i
  filter_upwards [hcell i] with x hx
  have h := (hLip.dist_le_mul x (z i)).trans (mul_le_mul_of_nonneg_left hx K.coe_nonneg)
  simpa only [Real.dist_eq] using! h

omit [MetricSpace X] in

theorem L2_tendsto_of_squared_error (ν : Measure X) (f : ℕ → X → ℝ) (ψ : X → ℝ)
    (hf : ∀ k, MemLp (f k) 2 ν) (hψ : MemLp ψ 2 ν)
    (herror : Tendsto (fun k => ∫ x, (f k x - ψ x) ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun k => (hf k).toLp (f k)) atTop (𝓝 (hψ.toLp ψ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [herror.eventually (gt_mem_nhds (show (0 : ℝ) < ε ^ 2 by positivity))]
    with k hk
  rw [← toLp_dist_sq_eq_integral ν (f k) ψ (hf k) hψ] at hk
  nlinarith [dist_nonneg (x := (hf k).toLp (f k)) (y := hψ.toLp ψ)]

end

end RieszRectifiability

end OAI
