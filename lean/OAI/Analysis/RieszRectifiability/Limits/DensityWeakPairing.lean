import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.DensityCancellation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem weak_L2_pairings_cancel_density {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f)
    (U : Set α) (hU : MeasurableSet U)
    [IsFiniteMeasure ((μ.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)]
    (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (T : ℕ → α → ℝ) (v : α → ℝ)
    (hweak : ∀ g : α → ℝ, MemLp g 2 ((μ.withDensity (fun x => ENNReal.ofReal (f x))).restrict U) →
      Tendsto (fun j => ∫ x in U, T j x * g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) atTop
        (𝓝 (∫ x in U, v x * g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x)))))
    (g : α → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ x, |g x| ≤ B) :
    Tendsto (fun j => ∫ x in U, T j x * g x ∂μ) atTop (𝓝 (∫ x in U, v x * g x ∂μ)) := by
  have hpos : ∀ x, 0 < f x := fun x => hc.trans_le (hlower x)
  have hdiv := bounded_div_density_memLp
    ((μ.withDensity (fun x => ENNReal.ofReal (f x))).restrict U) f g hf hg c B hc hlower hB
  have h := hweak (fun x => g x / f x) hdiv
  simpa only [setIntegral_mul_div_density μ f hf hpos U hU] using! h

theorem weak_L2_pairings_cancel_density_add_correction {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f)
    (U : Set α) (hU : MeasurableSet U)
    [IsFiniteMeasure ((μ.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)]
    (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (T : ℕ → α → ℝ) (v : α → ℝ)
    (hweak : ∀ g : α → ℝ, MemLp g 2 ((μ.withDensity (fun x => ENNReal.ofReal (f x))).restrict U) →
      Tendsto (fun j => ∫ x in U, T j x * g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) atTop
        (𝓝 (∫ x in U, v x * g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x)))))
    (F : α → ℝ) (V : Set α) (b : ℝ)
    (hconstant : ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (f x)), x ∈ V → v x + F x = b)
    (g : α → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ x, |g x| ≤ B)
    (hgs : ∀ x, g x ≠ 0 → x ∈ V) (hgI : IntegrableOn g U μ)
    (hFI : IntegrableOn (fun x => F x * g x) U μ) :
    Tendsto (fun j => (∫ x in U, T j x * g x ∂μ) + ∫ x in U, F x * g x ∂μ)
      atTop (𝓝 (b * ∫ x in U, g x ∂μ)) := by
  have hlim := weak_L2_pairings_cancel_density μ f hf U hU c hc hlower T v hweak g hg B hB
  have hbase : ∀ᵐ x ∂μ, x ∈ V → v x + F x = b :=
    (positive_density_absolutelyContinuous μ f hf (fun x => hc.trans_le (hlower x))).ae_le hconstant
  have heq : (fun x => v x * g x) =ᵐ[μ.restrict U] (fun x => b * g x - F x * g x) := by
    filter_upwards [ae_restrict_of_ae hbase] with x hx
    by_cases hz : g x = 0
    · simp only [hz, mul_zero, sub_zero]
    · rw [← hx (hgs x hz)]
      ring
  have hvalue : (∫ x in U, v x * g x ∂μ) + (∫ x in U, F x * g x ∂μ) =
      b * ∫ x in U, g x ∂μ := by
    rw [integral_congr_ae heq, integral_sub (hgI.const_mul b) hFI, integral_const_mul]
    ring
  simpa only [hvalue] using! hlim.add_const (∫ x in U, F x * g x ∂μ)

end

end RieszRectifiability

end OAI
