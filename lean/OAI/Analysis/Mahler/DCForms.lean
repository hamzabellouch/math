import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- Multiplication by i, viewed as a real continuous linear map. -/
def complexStructure : E →L[ℝ] E :=
  (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

/-- The operator d^c as a real alternating one-form. -/
def dcForm (g : E → ℝ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
    ((- (1 / 4 : ℝ)) • (fderiv ℝ g x).comp complexStructure)

lemma dcForm_apply (g : E → ℝ) (x : E) (v : Fin 1 → E) :
    dcForm g x v = -(fderiv ℝ g x (Complex.I • v 0)) / 4 := by
  simp [dcForm, complexStructure]
  ring

theorem dcForm_complex_coe {g : E → ℝ} {x : E} (hg : DifferentiableAt ℝ g x) (v : Fin 1 → E) :
    (dcForm g x v : ℂ) =
      -(fderiv ℝ (fun y => (g y : ℂ)) x (Complex.I • v 0)) / 4 := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hg.hasFDerivAt
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at hc
  rw [dcForm_apply, hc.fderiv]
  simp

/-- The identity d^c log g = g^{-1} d^c g, with the real logarithm. -/
theorem dcForm_log {g : E → ℝ} {x : E} (hg : DifferentiableAt ℝ g x) (hp : 0 < g x) :
    dcForm (fun y => Real.log (g y)) x = (g x)⁻¹ • dcForm g x := by
  have hl := (Real.hasDerivAt_log hp.ne').comp_hasFDerivAt x hg.hasFDerivAt
  simp only [Function.comp_def] at hl
  ext v
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, dcForm_apply]
  rw [hl.fderiv]
  simp
  ring

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The usual pullback, defined using the actual derivative of the parametrization. -/
def pullbackForm {k : ℕ} (φ : V → E) (ω : E → E [⋀^Fin k]→L[ℝ] ℝ)
    (y : V) : V [⋀^Fin k]→L[ℝ] ℝ :=
  (ω (φ y)).compContinuousLinearMap (fderiv ℝ φ y)

/-- On a level parametrization, the actual pulled-back one-form scales by R^{-1}. -/
theorem pullback_dc_log_level {φ : V → E} {g : E → ℝ} {R : ℝ} {y : V}
    (hR : 0 < R) (hg : DifferentiableAt ℝ g (φ y)) (hlevel : g (φ y) = R) :
    pullbackForm φ (dcForm (fun x => Real.log (g x))) y =
      R⁻¹ • pullbackForm φ (dcForm g) y := by
  unfold pullbackForm
  rw [dcForm_log hg (hlevel ▸ hR), hlevel]
  ext v
  simp

/-- Taking the actual exterior derivative on a level chart preserves the
same factor. This uses a proved local equality, not a Stokes assumption. -/
theorem extDeriv_pullback_dc_log_level {φ : V → E} {g : E → ℝ} {R : ℝ} {s : Set V} {y : V}
    (hs : IsOpen s) (hy : y ∈ s) (hR : 0 < R)
    (hg : ∀ z ∈ s, DifferentiableAt ℝ g (φ z)) (hlevel : ∀ z ∈ s, g (φ z) = R) :
    extDeriv (pullbackForm φ (dcForm (fun x => Real.log (g x)))) y =
      R⁻¹ • extDeriv (pullbackForm φ (dcForm g)) y := by
  have he : pullbackForm φ (dcForm (fun x => Real.log (g x))) =ᶠ[𝓝 y]
      (fun z => R⁻¹ • pullbackForm φ (dcForm g) z) := by
    filter_upwards [hs.mem_nhds hy] with z hz
    exact pullback_dc_log_level hR (hg z hz) (hlevel z hz)
  rw [he.extDeriv_eq]
  exact extDeriv_smul R⁻¹ (pullbackForm φ (dcForm g))

/-- Boundary restriction of dd^c log g: the pullback of the
exterior derivative is R^{-1} times that of dd^c g. -/
theorem pullback_ddc_log_level {φ : V → E} {g : E → ℝ} {R : ℝ} {s : Set V} {y : V}
    (hs : IsOpen s) (hy : y ∈ s) (hR : 0 < R)
    (hg : ∀ z ∈ s, DifferentiableAt ℝ g (φ z)) (hlevel : ∀ z ∈ s, g (φ z) = R)
    (hφ : ContDiffAt ℝ 2 φ y)
    (hdc : DifferentiableAt ℝ (dcForm g) (φ y))
    (hlog : DifferentiableAt ℝ (dcForm (fun x => Real.log (g x))) (φ y)) :
    pullbackForm φ (extDeriv (dcForm (fun x => Real.log (g x)))) y =
      R⁻¹ • pullbackForm φ (extDeriv (dcForm g)) y := by
  have he := extDeriv_pullback_dc_log_level hs hy hR hg hlevel
  unfold pullbackForm at he ⊢
  rw [extDeriv_pullback hlog hφ (by simp), extDeriv_pullback hdc hφ (by simp)] at he
  exact he

end MahlerStokes

end

end OAI
