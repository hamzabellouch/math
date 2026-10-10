import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialGeometricAssembly
import OAI.Geometry.TamingCompatibility.Functional.HermitianRadialProfiles
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianGeometricCenter

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter
open scoped Manifold ContDiff SchwartzMap Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (p : X)
variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

lemma schwartz_fderiv_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (W : 𝓢(E,F)) (z : E) :
    ‖fderiv ℝ W z‖ ≤ SchwartzMap.seminorm ℝ 0 1 W := by
  simpa only [norm_iteratedFDeriv_one] using W.norm_iteratedFDeriv_le_seminorm ℝ 1 z

lemma schwartz_difference_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (W : 𝓢(E,F)) (z b : E) :
    ‖W z-W b‖ ≤ SchwartzMap.seminorm ℝ 0 1 W * ‖z-b‖ := by
  have h := lipschitzWith_of_nnnorm_fderiv_le (W.smooth ⊤ |>.differentiable (by simp))
    (C := ⟨SchwartzMap.seminorm ℝ 0 1 W, apply_nonneg _ _⟩)
    (fun z => schwartz_fderiv_bound W z)
  exact h.norm_sub_le z b

lemma hermitianCenterExtension_bounds {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain) :
    ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧
      (∀ z, ‖hermitianCenterExtension J p D hφ hc hφD z‖ ≤ M) ∧
      (∀ z, ‖fderiv ℝ (hermitianCenterExtension J p D hφ hc hφD) z‖ ≤ L) ∧
      (∀ z b, ‖hermitianCenterExtension J p D hφ hc hφD z -
        hermitianCenterExtension J p D hφ hc hφD b‖ ≤ L*‖z-b‖) := by
  let W := hermitianCenterExtension J p D hφ hc hφD
  exact ⟨_,_,apply_nonneg (SchwartzMap.seminorm ℝ 0 1) W,
    apply_nonneg (SchwartzMap.seminorm ℝ 0 0) W,
    W.norm_le_seminorm ℝ,schwartz_fderiv_bound W,schwartz_difference_bound W⟩

lemma hermitianCenterExtension_eventually_eq {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain)
    {z : Space} (hz : φ =ᶠ[𝓝 z] fun _ => 1) :
    (hermitianCenterExtension J p D hφ hc hφD : Space → Space →L[ℝ] Space) =ᶠ[𝓝 z]
      coordinateJ J p :=
  hz.mono fun _ hx => hermitianCenterExtension_eq J p D hφ hc hφD hx

end TamingCompatibility.GeometricChart

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_complexLine (J : AlmostComplexStructure X) (β : TwoForm X) (p : X)
    {y : Space} (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback β (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
      eval β ((extChartAt Model p).symm y) (mfderiv Model Model (extChartAt Model p).symm y v)
        (J.endomorphism _ (mfderiv Model Model (extChartAt Model p).symm y v)) := by
  have hi := coordinateJ_intertwine J p hy v
  change (inverseChartEquiv p y hy).toContinuousLinearMap (coordinateJ J p y v) =
    J.endomorphism _ ((inverseChartEquiv p y hy).toContinuousLinearMap v) at hi
  rw [inverseChartEquiv_coe] at hi
  change β _ ((mfderiv Model Model (extChartAt Model p).symm y) ∘ ![v,coordinateJ J p y v]) = _
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact hi

end TamingCompatibility.GeometricChart

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ContinuousAlternatingMap
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma closedLift_pullback_complexLine
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (a : antiPre A J α hs ht) (p : X) {y : Space}
    (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs a).val
      (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
      nonharmonicCorrectionLM A J α hs ht Gs p y a ![v,coordinateJ J p y v] := by
  change _ = ManifoldForms.pullback
    (exteriorDerivative (codifferential J α ht (Gs a).val.val)) (extChartAt Model p).symm y _
  rw [pullback_complexLine J _ p hy,pullback_complexLine J _ p hy]
  exact closedLiftOfInverse_complexLine A J α hs ht H Gs a _ _

lemma correctedDdc_pullback_complexLine
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    (p : X) {y : Space} (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback (correctedDdc A J α hs ht H Gs hf).val
      (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
    ManifoldForms.pullback (exteriorDerivative (complexDifferential J f))
      (extChartAt Model p).symm y ![v,coordinateJ J p y v] -
      nonharmonicCorrectionLM A J α hs ht Gs p y
        (smoothAntiProjection A J α hs ht (smoothDdc J hf)) ![v,coordinateJ J p y v] := by
  change ManifoldForms.pullback (_-_) _ _ _ = _
  change ManifoldForms.pullback (smoothDdc J hf).val _ _ _ -
    ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs
      (smoothAntiProjection A J α hs ht (smoothDdc J hf))).val _ _ _ = _
  rw [closedLift_pullback_complexLine A J α hs ht H Gs _ p hy]
  rfl

lemma form_complexLine_norm_le (β : MetricForms.Form Space 2) (K : Space →L[ℝ] Space)
    (v : Space) : ‖β ![v,K v]‖ ≤ ‖β‖*‖K‖*‖v‖^2 := by
  calc
    _ ≤ ‖β‖*(‖v‖*‖K v‖) := by simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using β.le_opNorm ![v,K v]
    _ ≤ ‖β‖*(‖v‖*(‖K‖*‖v‖)) := by gcongr; exact K.le_opNorm v
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def hermitianLogGradientProfile (K : E →L[ℝ] E) (s : ℝ) (z v : E) : ℝ :=
  (s^2+‖z‖^2+‖K z‖^2)⁻¹ * (⟪z,v⟫+⟪K z,K v⟫)
def hermitianSqrtGradientProfile (K : E →L[ℝ] E) (s : ℝ) (z v : E) : ℝ :=
  (Real.sqrt (s^2+‖z‖^2+‖K z‖^2))⁻¹ * (⟪z,v⟫+⟪K z,K v⟫)

lemma hermitianLogGradient_eq (K : E →L[ℝ] E) (s : ℝ) (z v : E) :
    hermitianLogGradientProfile K s z v =
      logGradientProfile s (hermitianGraph K z) (hermitianGraph K v) := by
  simp only [hermitianLogGradientProfile,logGradientProfile,hermitianGraph_norm_sq,
    hermitianGraph_inner,add_assoc]

lemma hermitianSqrtGradient_eq (K : E →L[ℝ] E) (s : ℝ) (z v : E) :
    hermitianSqrtGradientProfile K s z v =
      sqrtGradientProfile s (hermitianGraph K z) (hermitianGraph K v) := by
  simp only [hermitianSqrtGradientProfile,sqrtGradientProfile,hermitianGraph_norm_sq,
    hermitianGraph_inner,add_assoc]

lemma hermitianLogGradient_eq_fderiv (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) (z v : E) :
    hermitianLogGradientProfile K s z v = fderiv ℝ (hermitianLogPotential K s) z v := by
  rw [hermitianLogGradient_eq,logGradientProfile_eq_fderiv hs]
  change _ = fderiv ℝ (fun x => logPotential s (hermitianGraph K x)) z v
  rw [fderiv_fun_comp z ((logPotential_smooth hs).differentiable (by simp) _)
    (hermitianGraph K).differentiableAt,(hermitianGraph K).fderiv]
  rfl

lemma hermitianSqrtGradient_eq_fderiv (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) (z v : E) :
    hermitianSqrtGradientProfile K s z v = fderiv ℝ (hermitianSqrtPotential K s) z v := by
  rw [hermitianSqrtGradient_eq,sqrtGradientProfile_eq_fderiv hs]
  change _ = fderiv ℝ (fun x => sqrtPotential s (hermitianGraph K x)) z v
  rw [fderiv_fun_comp z ((sqrtPotential_smooth hs).differentiable (by simp) _)
    (hermitianGraph K).differentiableAt,(hermitianGraph K).fderiv]
  rfl

lemma hermitianLogGradient_scale (K : E →L[ℝ] E) {r s : ℝ} (hr : 0 < r) (z v : E) :
    r * hermitianLogGradientProfile K (r*s) (r • z) v = hermitianLogGradientProfile K s z v := by
  simp only [hermitianLogGradient_eq,map_smul]
  exact logGradientProfile_scale hr _ _

lemma hermitianSqrtGradient_scale (K : E →L[ℝ] E) {r s : ℝ} (hr : 0 < r) (z v : E) :
    hermitianSqrtGradientProfile K (r*s) (r • z) v = hermitianSqrtGradientProfile K s z v := by
  simp only [hermitianSqrtGradient_eq,map_smul]
  exact sqrtGradientProfile_scale hr _ _

end TamingCompatibility.RadialPotential

end
end

end
end

end OAI
