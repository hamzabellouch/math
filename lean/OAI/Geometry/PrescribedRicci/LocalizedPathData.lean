import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalMetricEntries
import OAI.Geometry.PrescribedRicci.PathUniformForcing

namespace OAI

/-! Localized Path Data. -/

section

 
noncomputable section
open Set Filter Topology Matrix LineDeriv
open scoped ContDiff SchwartzMap Classical ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X}

def cutMetric (g : KaehlerMetric A) (q : Fin A.count)
    (σ : ChartCutoff (A.euclideanChart q).target) (i j : Fin d) : 𝓢(EC d,ℂ) :=
  σ.product (A.euclideanChart q).open_target
    (contDiffOn_pi.mp (contDiffOn_pi.mp (GluingData.metric_euclidean_smooth g q) i) j)

omit [T2Space X] [CompactSpace X] in
lemma cutMetric_apply (g : KaehlerMetric A) (q : Fin A.count)
    (σ : ChartCutoff (A.euclideanChart q).target) (i j : Fin d) (y : EC d) :
    cutMetric g q σ i j y = σ y*g.matrix q (coordinateEquiv d y) i j := rfl

lemma localize_cutoff_germ (q : Fin A.count) (τ : ChartCutoff (A.euclideanChart q).target)
    (F : Smooth A) {y : EC d} (_hy : y ∈ (A.euclideanChart q).target)
    (hτ : (τ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1) :
    (localize A q (cutoffGlobal q τ) (cutoffGlobal_support q τ) F : EC d → ℂ) =ᶠ[𝓝 y]
      F ∘ (A.euclideanChart q).symm := by
  rw [localize_cutoff_product]
  filter_upwards [hτ] with x hx
  simp only [ChartCutoff.product_apply,hx,one_mul,Function.comp_apply]

lemma localized_hessian_germ (q : Fin A.count) (τ : ChartCutoff (A.euclideanChart q).target)
    (φ : SmoothRealFunction A) {y : EC d} (hy : y ∈ (A.euclideanChart q).target)
    (hτ : (τ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1) (i j : Fin d) :
    (hessianEntrySchwartz i j (localize A q (cutoffGlobal q τ) (cutoffGlobal_support q τ)
      (Smooth.ofReal φ)) : EC d → ℂ) =ᶠ[𝓝 y]
        (fun x => φ.hessian q (coordinateEquiv d x) i j) := by
  have hev := (localize_cutoff_germ q τ (Smooth.ofReal φ) hy hτ).eventuallyEq_nhds
  filter_upwards [hev,(A.euclideanChart q).open_target.mem_nhds hy] with x hx hxt
  let u : EC d → ℝ := φ.localExpression q ∘ coordinateEquiv d
  have hu : ContDiffAt ℝ ∞ u x := (φ.euclidean_smooth q).contDiffAt
    (by simpa only [ComplexAtlas.euclideanChart_target] using (A.euclideanChart q).open_target.mem_nhds hxt)
  have he : (Smooth.ofReal φ : X → ℂ) ∘ (A.euclideanChart q).symm = Complex.ofRealCLM ∘ u := rfl
  rw [he] at hx
  rw [hessianEntrySchwartz_real hu _ hx i j,pullBilin_hessian hu]
  have hcomp : u ∘ (coordinateEquiv d).symm = φ.localExpression q := by
    funext z; simp [u]
  rw [hcomp]
  rfl

lemma cutMetric_deform (g : KaehlerMetric A) (q : Fin A.count)
    (σ τ : ChartCutoff (A.euclideanChart q).target)
    (hτ : ∀ y ∈ tsupport (σ : EC d → ℂ), (τ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1)
    (φ : SmoothRealFunction A) (hp : g.PositivePotential φ) (i j : Fin d) :
    cutMetric (g.deform φ hp) q σ i j = cutMetric g q σ i j+
      SchwartzMap.smulLeftCLM ℂ σ.val (hessianEntrySchwartz i j
        (localize A q (cutoffGlobal q τ) (cutoffGlobal_support q τ) (Smooth.ofReal φ))) := by
  ext y
  simp only [_root_.add_apply, SchwartzMap.smulLeftCLM_apply_apply σ.val.hasTemperateGrowth, smul_eq_mul]
  by_cases hy : y ∈ tsupport (σ : EC d → ℂ)
  · have hh := (localized_hessian_germ q τ φ (σ.support_sub hy) (hτ y hy) i j).eq_of_nhds
    change σ y*(g.matrix q (coordinateEquiv d y) i j+φ.hessian q (coordinateEquiv d y) i j) =
      σ y*g.matrix q (coordinateEquiv d y) i j+σ y*_
    rw [hh,mul_add]
  · have hh : σ y = 0 := image_eq_zero_of_notMem_tsupport hy
    change σ y*_ = σ y*_+σ y*_
    rw [hh]; ring

lemma cutMetric_deform_germ (g : KaehlerMetric A) (q : Fin A.count)
    (σ τ : ChartCutoff (A.euclideanChart q).target) (φ : SmoothRealFunction A) (hp : g.PositivePotential φ)
    {y : EC d} (hy : y ∈ (A.euclideanChart q).target)
    (hσ : (σ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1)
    (hτ : (τ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1) (i j : Fin d) :
    (cutMetric (g.deform φ hp) q σ i j : EC d → ℂ) =ᶠ[𝓝 y]
      (fun x => cutMetric g q σ i j x+hessianEntrySchwartz i j
        (localize A q (cutoffGlobal q τ) (cutoffGlobal_support q τ) (Smooth.ofReal φ)) x) := by
  filter_upwards [hσ,localized_hessian_germ q τ φ hy hτ i j] with x hx hh
  simp only [cutMetric_apply,hx,one_mul]
  rw [hh]
  rfl

lemma schwartzWord_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ws : List E) (F : 𝓢(E,ℂ)) (hF : ∀ x, (F x).im = 0) :
    ∀ x, (schwartzWord ws F x).im = 0 := by
  induction ws with
  | nil => exact hF
  | cons v ws ih =>
    intro x
    let G := schwartzWord ws F
    have he : (fun y => (G y).im) = fun _ => (0:ℝ) := funext ih
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L v)
      ((Complex.imCLM.hasFDerivAt.comp x G.differentiableAt.hasFDerivAt).fderiv)
    change fderiv ℝ (fun y => (G y).im) x v = (fderiv ℝ G x v).im at hh
    rw [he] at hh
    simp only [schwartzWord,ContinuousLinearMap.comp_apply,lineDerivOpCLM_apply]
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change (fderiv ℝ G x v).im = 0
    rw [← hh]
    simp

lemma localize_cutoff_real (q : Fin A.count) (τ : ChartCutoff (A.euclideanChart q).target)
    (hτ : ∀ y, (τ y).im = 0) (φ : SmoothRealFunction A) :
    ∀ y, (localize A q (cutoffGlobal q τ) (cutoffGlobal_support q τ) (Smooth.ofReal φ) y).im = 0 := by
  intro y
  rw [localize_cutoff_product,ChartCutoff.product_apply]
  change (τ y*(φ.value ((A.euclideanChart q).symm y):ℂ)).im = 0
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,hτ,zero_mul,mul_zero,add_zero]
end GlobalElliptic

end
end

end OAI
