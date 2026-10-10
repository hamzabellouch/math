import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic
import OAI.Analysis.RieszRectifiability.Limits.CompactWeakConvergence

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem positive_nnreal_smul_support {d : ℕ} (μ : Measure (Ambient d))
    (c : ℝ≥0) (hc : 0 < c) : (c • μ).support = μ.support := by
  have hcE : 0 < (c : ℝ≥0∞) := by exact_mod_cast hc
  ext x
  rw [Metric.nhds_basis_ball.mem_measureSupport, Metric.nhds_basis_ball.mem_measureSupport]
  constructor
  · intro hx r hr
    have h := hx r hr
    rw [Measure.coe_nnreal_smul_apply] at h
    exact (ENNReal.mul_pos_iff.mp h).2
  · intro hx r hr
    rw [Measure.coe_nnreal_smul_apply]
    exact ENNReal.mul_pos_iff.mpr ⟨hcE, hx r hr⟩

theorem positive_nnreal_smul_admissibleRadius {d : ℕ} (μ : Measure (Ambient d))
    (c : ℝ≥0) (hc : 0 < c) (r : ℝ) :
    AdmissibleRadius (c • μ) r ↔ AdmissibleRadius μ r := by
  simp only [AdmissibleRadius, positive_nnreal_smul_support μ c hc]

theorem globalUpperGrowth_smul_nnreal {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ) (c : ℝ≥0) :
    GlobalUpperGrowth n ((c : ℝ) * G) (c • μ) := by
  refine ⟨mul_nonneg c.coe_nonneg hg.1, fun x r hr => ?_⟩
  rw [Measure.coe_nnreal_smul_apply]
  calc
    _ ≤ (c : ℝ≥0∞) * ENNReal.ofReal (G * r ^ n) := mul_le_mul_right (hg.2 x r hr) _
    _ = ENNReal.ofReal ((c : ℝ) * G * r ^ n) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg]
      congr 1
      ring

theorem lowerGrowth_smul_nnreal {d : ℕ} (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hC : 0 < C)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (c : ℝ≥0) (hc : 0 < c) :
    ∀ x ∈ (c • μ).support, ∀ r : ℝ, AdmissibleRadius (c • μ) r →
      ENNReal.ofReal (r ^ n / (C / (c : ℝ))) ≤ (c • μ) (ball x r) := by
  intro x hx r hr
  have hcR : 0 < (c : ℝ) := NNReal.coe_pos.mpr hc
  have hx' : x ∈ μ.support := by simpa only [positive_nnreal_smul_support μ c hc] using! hx
  have hr' := (positive_nnreal_smul_admissibleRadius μ c hc r).mp hr
  rw [Measure.coe_nnreal_smul_apply]
  calc
    _ = (c : ℝ≥0∞) * ENNReal.ofReal (r ^ n / C) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg]
      congr 1
      field_simp
    _ ≤ _ := mul_le_mul_right (hlower x hx' r hr') _

theorem compactTestConvergence_smul_nnreal {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (hlocal : CompactTestConvergence μ ν) (c : ℝ≥0) :
    CompactTestConvergence (fun j => c • μ j) (c • ν) := by
  intro g
  simpa only [integral_smul_nnreal_measure, smul_eq_mul] using! (hlocal g).const_mul (c : ℝ)

theorem compactTestConvergence_cancel_scalar_limit {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν σ : Measure (Ambient d))
    (hlocal : CompactTestConvergence μ ν) (q : ℝ)
    (hν : ν = ENNReal.ofReal q • σ) (c : ℝ≥0) (hcq : (c : ℝ) * q = 1) :
    CompactTestConvergence (fun j => c • μ j) σ := by
  have h := compactTestConvergence_smul_nnreal μ ν hlocal c
  have heq : c • ν = σ := by
    rw [hν]
    change (c : ℝ≥0∞) • (ENNReal.ofReal q • σ) = σ
    rw [smul_smul]
    have hcoef : (c : ℝ≥0∞) * ENNReal.ofReal q = 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg, hcq, ENNReal.ofReal_one]
    rw [hcoef, one_smul]
  simpa only [heq] using! h

end

end RieszRectifiability

end OAI
