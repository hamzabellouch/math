import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! # Applying a locally bounded strongly holomorphic operator field -/

namespace KadisonKastler

open Filter
open scoped Topology

variable {X E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A locally bounded strong operator limit can be evaluated on converging vectors. -/
theorem tendsto_strong_apply {l : Filter X} {A : X → E →L[ℂ] F} {A₀ : E →L[ℂ] F}
    (hA : ∀ y, Tendsto (fun s => A s y) l (𝓝 (A₀ y)))
    {B : ℝ} (hB : ∀ᶠ s in l, ‖A s‖ ≤ B)
    {x : X → E} {x₀ : E} (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun s => A s (x s)) l (𝓝 (A₀ x₀)) := by
  have hzero : Tendsto (fun s => A s (x s - x₀)) l (𝓝 0) := by
    apply squeeze_zero_norm' (hB.mono fun s hs =>
      ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _)))
    have hz : Tendsto (fun s => ‖x s - x₀‖) l (𝓝 0) := by
      simpa using (hx.sub_const x₀).norm
    simpa using hz.const_mul B
  convert hzero.add (hA x₀) using 1
  · funext s
    rw [map_sub, sub_add_cancel]
  · rw [zero_add]

/-- Strong holomorphicity and a local operator bound suffice for the product rule. -/
theorem differentiableAt_strong_apply {A : ℂ → E →L[ℂ] F} {z₀ : ℂ}
    (hA : ∀ y, DifferentiableAt ℂ (fun z => A z y) z₀)
    {B : ℝ} (hB : ∀ᶠ z in 𝓝 z₀, ‖A z‖ ≤ B)
    {x : ℂ → E} (hx : DifferentiableAt ℂ x z₀) :
    DifferentiableAt ℂ (fun z => A z (x z)) z₀ := by
  apply HasDerivAt.differentiableAt
    (f' := A z₀ (deriv x z₀) + deriv (fun z => A z (x z₀)) z₀)
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim := tendsto_strong_apply
    (fun y => (hA y).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hB.filter_mono nhdsWithin_le_nhds) hx.hasDerivAt.tendsto_slope
  have hsum := hlim.add (hA (x z₀)).hasDerivAt.tendsto_slope
  convert hsum using 1
  funext z
  simp only [slope_def_module, map_smul, map_sub, smul_sub]
  module

end KadisonKastler

end OAI
