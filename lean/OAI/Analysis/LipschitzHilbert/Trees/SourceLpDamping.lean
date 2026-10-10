import OAI.Analysis.LipschitzHilbert.Estimates.DampedSimplexBounds
import OAI.Analysis.LipschitzHilbert.Trees.SourceSimplexLp

namespace OAI

/-! Constant scalar damping acts exactly on the Lp root. The vertex
estimate on the prescribed imaginary ball therefore extends to the whole
tube using the manuscript's Gaussian tail estimate. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert
variable {X κ ι : Type*} [MeasurableSpace X] [Fintype κ] [Fintype ι]

theorem source_lp_root_smul (μ : Measure X) (F : X → EuclideanSpace ℂ κ)
    (c : ℂ) (p : ℝ) (hp : 0 < p) :
    (∫ x, ‖c • F x‖^p ∂μ)^(1/p) = ‖c‖*(∫ x, ‖F x‖^p ∂μ)^(1/p) := by
  have heq : (∫ x, ‖c • F x‖^p ∂μ) = ‖c‖^p*(∫ x, ‖F x‖^p ∂μ) := by
    simp_rw [norm_smul,Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
    exact integral_const_mul _ _
  rw [heq,Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _)
    (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg c),mul_one_div_cancel hp.ne',Real.rpow_one]

theorem source_lp_power_smul_integrable (μ : Measure X) (F : X → EuclideanSpace ℂ κ)
    (c : ℂ) (p : ℝ) (hF : Integrable (fun x => ‖F x‖^p) μ) :
    Integrable (fun x => ‖c • F x‖^p) μ := by
  simp_rw [norm_smul,Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
  exact hF.const_mul _

theorem eventually_source_damped_vertex_root (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (μ : Measure X) (F : X → EuclideanSpace ℂ κ)
      (a eta : ι → ℝ) (mu P p : ℝ),
      (∀ i, 0 ≤ a i) → (∑ i, a i = mu) → 0 ≤ mu → mu ≤ 1 → 0 ≤ P → 0 < p →
      (∫ x, ‖F x‖^p ∂μ)^(1/p) ≤
        P*(1+Real.sqrt (∑ i, (eta i)^2))*Real.exp (C*Real.sqrt L) →
      (Real.sqrt (∑ i, (eta i)^2) ≤ L^2 → (∫ x, ‖F x‖^p ∂μ)^(1/p) ≤ P) →
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint a eta) • F x‖^p ∂μ)^(1/p) ≤
        Real.exp 1*P := by
  filter_upwards [eventually_damped_vertex_bound (ι := ι) C hC] with L hL
  intro μ F a eta mu P p ha hsum hmu hmu1 hP hp hcrude hsmall
  let V := (∫ x, ‖F x‖^p ∂μ)^(1/p)
  have hV : 0 ≤ V := Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  have hnorm : ‖(V:ℂ)‖ = V := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hV]
  have h := hL a eta mu P (V:ℂ) ha hsum hmu hmu1 hP
    (by simpa only [hnorm] using hcrude) (by simpa only [hnorm] using hsmall)
  rw [norm_mul,hnorm] at h
  rwa [source_lp_root_smul μ F _ p hp]

end LipschitzHilbert

end

end OAI
