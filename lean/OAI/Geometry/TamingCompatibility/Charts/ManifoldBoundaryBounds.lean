import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeL2Coefficients
import OAI.Geometry.TamingCompatibility.Concentration.ActivationMeasureBounds

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma log_boundary_eval (J : AlmostComplexStructure X) (f : X → ℝ)
    (hf : MDifferentiable Model 𝓘(ℝ,ℝ) f) (hpos : ∀ x, 0 ≤ f x)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (θ : Form X 1) (x : X) (v : TangentSpace Model x) :
    |eval (ManifoldForms.wedgeOne
      (scalarDifferential (fun x => SummableCutoff.logActivation ε δ (f x))) θ) x v (J.endomorphism x v)| =
      (ε/(δ+f x))*|eval (ManifoldForms.wedgeOne (scalarDifferential f) θ) x v (J.endomorphism x v)| := by
  rw [scalarDifferential_logActivation hf hδ hpos,wedgeOne_fun_smul_left]
  simp only [eval,ContinuousAlternatingMap.smul_apply,smul_eq_mul,abs_mul,
    abs_of_nonneg (show 0 ≤ ε/(δ+f x) by have := hpos x; positivity)]

lemma saturation_boundary_eval (J : AlmostComplexStructure X) (c : ℕ → X → ℝ)
    (hc : ∀ k, MDifferentiable Model 𝓘(ℝ,ℝ) (c k)) (hpos : ∀ k x, 0 ≤ c k x)
    (θ : Form X 1) (n N : ℕ) (x : X) (v : TangentSpace Model x) :
    |eval (ManifoldForms.wedgeOne (scalarDifferential (SummableCutoff.saturation c n N)) θ) x v (J.endomorphism x v)| ≤
      ∑ k ∈ Finset.range N, |eval (ManifoldForms.wedgeOne (scalarDifferential (c (k+n))) θ) x v (J.endomorphism x v)| := by
  rw [scalarDifferential_saturation hc,wedgeOne_fun_smul_left]
  have he : eval (fun x => Real.exp (-(∑ k ∈ Finset.range N, c (k+n) x)) •
      ManifoldForms.wedgeOne (fun x => ∑ k ∈ Finset.range N, scalarDifferential (c (k+n)) x) θ x) x v (J.endomorphism x v) =
      Real.exp (-(∑ k ∈ Finset.range N, c (k+n) x)) *
        (∑ k ∈ Finset.range N, eval (ManifoldForms.wedgeOne (scalarDifferential (c (k+n))) θ) x v (J.endomorphism x v)) := by
    have hh : (fun x => ∑ k ∈ Finset.range N, scalarDifferential (c (k+n)) x) =
        ∑ k ∈ Finset.range N, scalarDifferential (c (k+n)) := by funext x; simp only [Finset.sum_apply]
    rw [hh,wedgeOne_sum_left]
    simp only [eval,Finset.sum_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul]
    erw [ContinuousAlternatingMap.sum_apply]
  rw [he,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply (mul_le_of_le_one_left (abs_nonneg _) ?_).trans (Finset.abs_sum_le_sum_abs _ _)
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun k _ => hpos (k+n) x))

variable [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (ht : Tames α J) (E : ∀ p : A.centers, ParametrixData J α ht p.val)

omit [T2Space X] [CompactSpace X] in
lemma log_boundary_norm (f : X → ℝ) (hf : MDifferentiable Model 𝓘(ℝ,ℝ) f)
    (hpos : ∀ x, 0 ≤ f x) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (θ : Form X 1) (x : X) :
    ‖normalizedFrameEncode A J α ht E x (ManifoldForms.wedgeOne
      (scalarDifferential (fun x => SummableCutoff.logActivation ε δ (f x))) θ x)‖ =
      (ε/(δ+f x))*‖normalizedFrameEncode A J α ht E x (ManifoldForms.wedgeOne (scalarDifferential f) θ x)‖ := by
  rw [scalarDifferential_logActivation hf hδ hpos,wedgeOne_fun_smul_left]
  erw [_root_.map_smul]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ ε/(δ+f x) by have := hpos x; positivity)]

omit [T2Space X] [CompactSpace X] in
lemma saturation_boundary_norm (c : ℕ → X → ℝ)
    (hc : ∀ k, MDifferentiable Model 𝓘(ℝ,ℝ) (c k)) (hpos : ∀ k x, 0 ≤ c k x)
    (θ : Form X 1) (n N : ℕ) (x : X) :
    ‖normalizedFrameEncode A J α ht E x
      (ManifoldForms.wedgeOne (scalarDifferential (SummableCutoff.saturation c n N)) θ x)‖ ≤
      ∑ k ∈ Finset.range N, ‖normalizedFrameEncode A J α ht E x
        (ManifoldForms.wedgeOne (scalarDifferential (c (k+n))) θ x)‖ := by
  rw [scalarDifferential_saturation hc,wedgeOne_fun_smul_left]
  have hh : (fun x => ∑ k ∈ Finset.range N, scalarDifferential (c (k+n)) x) =
      ∑ k ∈ Finset.range N, scalarDifferential (c (k+n)) := by funext x; simp only [Finset.sum_apply]
  rw [hh,wedgeOne_sum_left]
  simp only [Finset.sum_apply]
  erw [_root_.map_smul,_root_.map_sum]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
    (norm_sum_le (Finset.range N) (fun k => normalizedFrameEncode A J α ht E x
      (ManifoldForms.wedgeOne (scalarDifferential (c (k+n))) θ x)))
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun k _ => hpos (k+n) x))
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
