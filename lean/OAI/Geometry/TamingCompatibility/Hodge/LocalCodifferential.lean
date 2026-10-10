import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ComplexEquiv

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.MetricForms
open MetricModel ContinuousAlternatingMap
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_add_left (g : Metric E) {k : ℕ} (a b c : Form E k) :
    pairing g (a+b) c = pairing g a c + pairing g b c := by
  change FormMetric.pairing (MetricHodge.formEquiv g k (a+b)) (MetricHodge.formEquiv g k c) = _
  rw [_root_.map_add]
  simp only [FormMetric.pairing,_root_.map_add,inner_add_left]
  rfl
end TamingCompatibility.MetricForms

namespace TamingCompatibility.MetricHodge
open MetricModel MetricForms ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local instance {k : ℕ} : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective
local instance {k : ℕ} : FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective ContinuousAlternatingMap.toContinuousMultilinearMapLinear
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective

lemma starThree_add (g : Metric E) (F : MetricForms.Form E 2) (a b : MetricForms.Form E 3) :
    starThree g F (a+b) = starThree g F a + starThree g F b := by
  ext v
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv,ContinuousAlternatingMap.add_apply,starThree_apply,starThree_apply,starThree_apply,
    pairing_add_left]
  ring
lemma starThree_smul (g : Metric E) (F : MetricForms.Form E 2) (t : ℝ) (a : MetricForms.Form E 3) :
    starThree g F (t • a) = t • starThree g F a := by
  ext v
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv,ContinuousAlternatingMap.smul_apply,starThree_apply,starThree_apply,pairing_smul_left]
  simp only [smul_eq_mul]
  ring

def starThreeCLM (g : Metric E) (F : MetricForms.Form E 2) :
    MetricForms.Form E 3 →L[ℝ] MetricForms.Form E 1 :=
  LinearMap.toContinuousLinearMap {
    toFun := starThree g F
    map_add' := starThree_add g F
    map_smul' := fun t a => starThree_smul g F t a }
lemma starThreeCLM_apply (g : Metric E) (F : MetricForms.Form E 2) (a : MetricForms.Form E 3) :
    starThreeCLM g F a = starThree g F a := rfl
end TamingCompatibility.MetricHodge

namespace TamingCompatibility.SmoothHodge
open MetricModel MetricForms MetricHodge
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
local instance {k : ℕ} : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective
local instance {k : ℕ} : FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective ContinuousAlternatingMap.toContinuousMultilinearMapLinear
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective

lemma starThreeCLM_contDiffOn (g : D → Metric E) (J : D → E →L[ℝ] E)
    (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    {F : D → MetricForms.Form E 2} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun x => starThreeCLM (g x) (F x)) U := by
  apply contDiffOn_clm_apply.mpr
  intro a
  exact starThree_contDiffOn g J hdim hU hg hJ hJs hgJ hF contDiffOn_const
end TamingCompatibility.SmoothHodge

namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma extDeriv_variable_smul {k : ℕ} {f : E → ℝ} {a : E → Form (E := E) k} {x : E}
    (hf : DifferentiableAt ℝ f x) (ha : DifferentiableAt ℝ a x) :
    extDeriv (fun y => f y • a y) x = f x • extDeriv a x + wedgeOne (fderiv ℝ f x) (a x) := by
  simp only [extDeriv,fderiv_fun_smul hf ha,alternatizeUncurryFin_add,
    alternatizeUncurryFin_smul,wedgeOne]
end TamingCompatibility.ExteriorForms

namespace TamingCompatibility.ManifoldHodge
open Bundle ContinuousAlternatingMap ManifoldForms ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_codifferential_antiInvariant (J : AlmostComplexStructure X) (α : TwoForm X)
    (ht : Tames α J) {a : TwoForm X} (ha : IsSmooth a) (hanti : antiInvariantPart J a = a)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z =
      -MetricHodge.starThree (coordinateMetric J α ht p z)
        (TamingCompatibility.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (extDeriv (ManifoldForms.pullback a (extChartAt Model p).symm) z) := by
  have hstar : starTwo J α ht a = a := by
    rw [← hanti]
    exact starTwo_antiInvariant J α ht a
  change ((-(starThree J α ht (exteriorDerivative (starTwo J α ht a))))
    ((extChartAt Model p).symm z)).compContinuousLinearMap _ = _
  rw [hstar]
  have hneg (b : ManifoldForms.Form X 1) :
      ManifoldForms.pullback (-b) (extChartAt Model p).symm z =
        -ManifoldForms.pullback b (extChartAt Model p).symm z := by ext v; rfl
  change ManifoldForms.pullback (-(starThree J α ht (exteriorDerivative a)))
    (extChartAt Model p).symm z = _
  rw [hneg,pullback_starThree J α ht _ p hz,
    pullback_exteriorDerivative a ha (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm p) hz]
  congr 2
  exact extDerivWithin_eq_of_mem (isOpen_extChartAt_target p) hz
end TamingCompatibility.ManifoldHodge

end
end

end
end
end

end OAI
