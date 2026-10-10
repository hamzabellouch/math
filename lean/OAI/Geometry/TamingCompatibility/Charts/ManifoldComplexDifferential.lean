import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.NormalSymbol
import OAI.Geometry.TamingCompatibility.DifferentialForms.FirstOrderAntiDdc

namespace OAI


noncomputable section
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap ManifoldHodge Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def complexDifferential (J : AlmostComplexStructure X) (f : X → ℝ) : Form X 1 := fun x =>
  ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1)
    (-(mfderiv Model 𝓘(ℝ,ℝ) f x).comp (J.endomorphism x))

lemma pullback_complexDifferential (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) :
    pullback (complexDifferential J f) (extChartAt Model p).symm z =
      ExteriorForms.dc (coordinateJ J p) (f ∘ (extChartAt Model p).symm) z := by
  have hg := (((contMDiffOn_extChartAt_symm (n := ∞) p) z hz).contMDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hz)).mdifferentiableAt (by simp)
  unfold ExteriorForms.dc
  rw [← mfderiv_eq_fderiv,mfderiv_comp z (hf.mdifferentiable (by simp) _) hg]
  ext v
  have hi := coordinateJ_intertwine J p hz (v 0)
  change (inverseChartEquiv p z hz).toContinuousLinearMap (coordinateJ J p z (v 0)) =
    J.endomorphism _ ((inverseChartEquiv p z hz).toContinuousLinearMap (v 0)) at hi
  rw [inverseChartEquiv_coe] at hi
  change -(mfderiv Model 𝓘(ℝ,ℝ) f _) (J.endomorphism _ (mfderiv Model Model _ z (v 0))) =
    -(mfderiv Model 𝓘(ℝ,ℝ) f _) (mfderiv Model Model _ z (coordinateJ J p z (v 0)))
  exact congrArg (fun w => -(mfderiv Model 𝓘(ℝ,ℝ) f ((extChartAt Model p).symm z)) w) hi.symm

lemma complexDifferential_smooth (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) : Smooth (complexDifferential J f) := by
  apply smooth_of_charts
  intro p
  have hc : ContDiffOn ℝ ∞ (f ∘ (extChartAt Model p).symm) (extChartAt Model p).target :=
    (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm p)).contDiffOn
  have hd := hc.fderiv_of_isOpen (isOpen_extChartAt_target p) (m := ∞) (by simp)
  have he := ((ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1)).contDiff.comp_contDiffOn
    ((hd.clm_comp (coordinateJ_smooth J p)).neg))
  apply he.congr
  intro z hz
  exact pullback_complexDifferential J hf p hz

lemma pullback_ddc (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) :
    pullback (exteriorDerivative (complexDifferential J f)) (extChartAt Model p).symm z =
      extDeriv (ExteriorForms.dc (coordinateJ J p) (f ∘ (extChartAt Model p).symm)) z := by
  rw [pullback_exteriorDerivative _ (complexDifferential_smooth J hf) (isOpen_extChartAt_target p)
    (contMDiffOn_extChartAt_symm p) hz,extDerivWithin_eq_of_mem (isOpen_extChartAt_target p) hz]
  apply Filter.EventuallyEq.extDeriv_eq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with y hy
  exact pullback_complexDifferential J hf p hy

lemma anti_ddc_chart_first_order (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    pullback (antiInvariantPart J (exteriorDerivative (complexDifferential J f)))
      (extChartAt Model p).symm z ![u,v] =
      (1/2:ℝ) * fderiv ℝ (f ∘ (extChartAt Model p).symm) z
        ((fderiv ℝ (coordinateJ J p) z v) u - (fderiv ℝ (coordinateJ J p) z u) v +
          (fderiv ℝ (coordinateJ J p) z (coordinateJ J p z u)) (coordinateJ J p z v) -
          (fderiv ℝ (coordinateJ J p) z (coordinateJ J p z v)) (coordinateJ J p z u)) := by
  rw [pullback_antiInvariantPart J _ p hz,pullback_ddc J hf p hz]
  have hcInf : ContDiffAt ℝ ∞ (f ∘ (extChartAt Model p).symm) z :=
    (((hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm (n := ∞) p)).contDiffOn) z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)
  have hc : ContDiffAt ℝ 2 (f ∘ (extChartAt Model p).symm) z := hcInf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hj : DifferentiableAt ℝ (coordinateJ J p) z :=
    (((coordinateJ_smooth J p) z hz).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have he : (fun i : Fin 2 => coordinateJ J p z (![u,v] i)) =
      ![coordinateJ J p z u,coordinateJ J p z v] := by
    ext i; fin_cases i <;> rfl
  simp only [ContinuousAlternatingMap.smul_apply,ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,Function.comp_def,he,smul_eq_mul]
  simpa only [Function.comp_def,div_eq_mul_inv,mul_comm,one_mul] using
    ExteriorForms.anti_ddc_first_order hc hj (coordinateJ_square J p hz) u v
end TamingCompatibility.ManifoldForms

end

end OAI
