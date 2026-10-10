import OAI.Analysis.CircleDomains.Sobolev.L2ProductConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt
import OAI.Analysis.CircleDomains.Sobolev.SphericalGradientEnergyNorm

namespace OAI

/-! Vanishing quadratic energy forces every fixed L² pairing to vanish. -/
open Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem tendsto_L2_pairing_zero_of_energy
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : ℕ → X → ℝ} (hg : ∀ n, MemLp (g n) 2 μ)
    {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0))
    (he : ∀ n, (∫ x, g n x^2 ∂μ) ≤ b n)
    {w : X → ℝ} (hw : MemLp w 2 μ) :
    Tendsto (fun n => ∫ x, g n x*w x ∂μ) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => (eLpNorm (g n) 2 μ).toReal^2) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    · exact fun n => sq_nonneg _
    · intro n
      change (eLpNorm (g n) 2 μ).toReal^2 ≤ b n
      rw [← integral_sq_eq_eLpNorm_toReal_sq (hg n)]
      exact he n
  have hn : Tendsto (fun n => (eLpNorm (g n) 2 μ).toReal) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      Real.sqrt_zero] using h
  apply squeeze_zero_norm' _ (by simpa using hn.mul_const (eLpNorm w 2 μ).toReal)
  exact Eventually.of_forall (fun n => by
    simpa only [Real.norm_eq_abs] using abs_integral_mul_le_eLpNorm_two (hg n) hw)

end CircleDomainRigidity

end

end OAI
