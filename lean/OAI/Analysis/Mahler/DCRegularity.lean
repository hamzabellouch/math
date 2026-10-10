import OAI.Analysis.Mahler.DCForms
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The normalized d^c form of a C2 real potential is C1. -/
theorem contDiffAt_dcForm {τ : E → ℝ} {x : E} (hτ : ContDiffAt ℝ 2 τ x) :
    ContDiffAt ℝ 1 (dcForm τ) x := by
  have hD : ContDiffAt ℝ 1 (fderiv ℝ τ) x := hτ.fderiv_right (by norm_num)
  have hC : ContDiffAt ℝ 1 (fun y => (fderiv ℝ τ y).comp complexStructure) x :=
    hD.clm_comp contDiffAt_const
  have hS : ContDiffAt ℝ 1 (fun y => (-(1/4 : ℝ)) • (fderiv ℝ τ y).comp complexStructure) x :=
    (contDiffAt_const (c := -(1/4 : ℝ))).smul hC
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).contDiff.contDiffAt.comp x hS

 theorem contDiffAt_dcForm_log {τ : E → ℝ} {x : E}
    (hτ : ContDiffAt ℝ 2 τ x) (hp : 0 < τ x) :
    ContDiffAt ℝ 1 (dcForm (fun y => Real.log (τ y))) x :=
  contDiffAt_dcForm (hτ.log hp.ne')

end MahlerStokes

end

end OAI
