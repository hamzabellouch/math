import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.FormGenerator
import OAI.Geometry.WeakHessian.LocalBounds.SubConst

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile185
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.generator_energy_tendsto_zero
    {ι : Type*} {l : Filter ι} {u A : ι → E}
    (hg : ∀ᶠ i in l,hQ.IsFormGenerator (u i) (A i))
    (hu : Tendsto u l (𝓝 0)) (hA : Tendsto A l (𝓝 0)) :
    Tendsto (fun i => (Q (u i)).toReal) l (𝓝 0) := by
  have hh : Tendsto (fun i => ‖A i‖*‖u i‖/2) l (𝓝 0) := by
    simpa using (hA.norm.mul hu.norm).div_const 2
  apply squeeze_zero' (Eventually.of_forall fun i => ENNReal.toReal_nonneg) _ hh
  filter_upwards [hg] with i hi
  have hb := hQ.formGenerator_energy_bound hi
  linarith

lemma ClosedQuadraticEnergy.generator_derivative_energy
    {u A : ℝ → E} {u' A' : E} {a : ℝ}
    (hu : HasDerivAt u u' a) (hA : HasDerivAt A A' a)
    (hg : ∀ᶠ t in 𝓝 a,hQ.IsFormGenerator (u t) (A t))
    (hg' : hQ.IsFormGenerator u' A') :
    Tendsto (fun t => (Q ((t-a)⁻¹ • (u t-u a)-u')).toReal) (𝓝[≠] a) (𝓝 0) := by
  have hga := mem_of_mem_nhds hg
  apply hQ.generator_energy_tendsto_zero
    (A := fun t => (t-a)⁻¹ • (A t-A a)-A')
  · filter_upwards [hg.filter_mono nhdsWithin_le_nhds] with t ht
    exact hQ.formGenerator_sub
      (hQ.formGenerator_smul (t-a)⁻¹ (hQ.formGenerator_sub ht hga)) hg'
  · simpa only [slope_def_module,sub_self] using hu.tendsto_slope.sub_const u'
  · simpa only [slope_def_module,sub_self] using hA.tendsto_slope.sub_const A'
end WeakHessianFunctional

end
end InlinedFile185

end OAI
