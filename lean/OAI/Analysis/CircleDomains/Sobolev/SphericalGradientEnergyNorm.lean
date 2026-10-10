import OAI.Analysis.CircleDomains.Sobolev.CoordinateEstimates
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! Express the actual spherical Dirichlet energy through its two L²
partial-derivative norms. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

theorem integral_sq_eq_eLpNorm_toReal_sq
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {f : A → ℝ} (hf : MemLp f 2 μ) :
    (∫x, f x ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  calc
    _ = ∫x, inner ℝ (hf.toLp f x) (hf.toLp f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := (L2.inner_def _ _).symm
    _ = ‖hf.toLp f‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = _ := by rw [Lp.norm_toLp]

theorem spherical_gradient_energy_eq_norms
    {μ : Measure (ℝ × ℝ)} {f : (ℝ × ℝ) → ℝ}
    (hf : MemLp (FiniteTransfer.planarGradient f) 2 μ) :
    (∫x, FiniteTransfer.gradientEnergy f (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x ∂μ) =
      (eLpNorm (fun x => (fderiv ℝ f x) (1, 0)) 2 μ).toReal ^ 2 +
        (eLpNorm (fun x => (fderiv ℝ f x) (0, 1)) 2 μ).toReal ^ 2 := by
  have hx := hf.fst
  have hy := hf.snd
  calc
    _ = ∫x, (FiniteTransfer.planarGradient f x).1 ^ 2 +
        (FiniteTransfer.planarGradient f x).2 ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (FiniteTransfer.gradientEnergy_spherical f)
    _ = (∫x, (FiniteTransfer.planarGradient f x).1 ^ 2 ∂μ) +
        (∫x, (FiniteTransfer.planarGradient f x).2 ^ 2 ∂μ) :=
      integral_add hx.integrable_sq hy.integrable_sq
    _ = _ := by rw [integral_sq_eq_eLpNorm_toReal_sq hx, integral_sq_eq_eLpNorm_toReal_sq hy]; rfl

end CircleDomainRigidity

end

end OAI
