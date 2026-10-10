import Mathlib

namespace OAI
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma hasDerivAt_moving_eval {u : ℝ → (V →ᵇ ℂ)} {p : V →ᵇ ℂ} {t : ℝ}
    (hu : HasDerivAt u p t) {y : ℝ → V} {y' : V} (hy : HasDerivAt y y' t)
    (hx : DifferentiableAt ℝ (u t : V → ℂ) (y t)) :
    HasDerivAt (fun r => u r (y r)) (p (y t)+fderiv ℝ (u t : V → ℂ) (y t) y') t := by
  let : NormedAddCommGroup (V →ᵇ ℂ) := inferInstance
  let : NormedSpace ℝ (V →ᵇ ℂ) := inferInstance
  have h0 := hx.hasFDerivAt.comp_hasDerivAt t hy
  have he : Continuous (fun z : (V →ᵇ ℂ) × V => z.1 z.2) := continuous_eval
  have hz : Tendsto (fun r => (slope u t r,y r)) (𝓝[≠] t) (𝓝 (p,y t)) :=
    hu.tendsto_slope.prodMk_nhds (hy.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hp : Tendsto (fun r => slope u t r (y r)) (𝓝[≠] t) (𝓝 (p (y t))) :=
    (he.tendsto (p,y t)).comp hz
  apply hasDerivAt_iff_tendsto_slope.mpr
  convert hp.add h0.tendsto_slope using 1
  funext r
  simp only [slope,vsub_eq_sub,BoundedContinuousFunction.coe_smul,
    BoundedContinuousFunction.coe_sub,Pi.sub_apply,Function.comp_apply]
  rw [←smul_add]
  congr 1
  abel
end ParametrixDilation

end

end OAI
