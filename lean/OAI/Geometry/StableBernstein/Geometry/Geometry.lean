import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Tactic.Linarith
import OAI.Geometry.StableBernstein.Model

namespace OAI

noncomputable section
open scoped ContDiff
open Manifold

namespace StableBernstein.W01

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E6 M]

attribute [local instance] coordinateTangentNorm

attribute [local instance] coordinateTangentNormedSpace

lemma source_dimension : Module.finrank ℝ E6 = 6 := finrank_euclideanSpace_fin

lemma ambient_dimension : Module.finrank ℝ E7 = 7 := finrank_euclideanSpace_fin

lemma SmoothImmersion.mdifferentiable {F : M → E7} (hF : SmoothImmersion F) :
    MDifferentiable I6 I7 F := hF.smooth.mdifferentiable (by simp)

lemma inducedMetric_nonneg (F : M → E7) (x : M) (v : TangentSpace I6 x) :
    0 ≤ inducedMetric F x v v := real_inner_self_nonneg

lemma inducedMetric_add_left (F : M → E7) (x : M) (u v w : TangentSpace I6 x) :
    inducedMetric F x (u + v) w = inducedMetric F x u w + inducedMetric F x v w := by
  simp [inducedMetric, inner_add_left]

lemma inducedMetric_smul_left (F : M → E7) (x : M) (c : ℝ) (v w : TangentSpace I6 x) :
    inducedMetric F x (c • v) w = c * inducedMetric F x v w := by
  simp [inducedMetric, inner_smul_left]

lemma SmoothImmersion.inducedMetric_self_eq_zero_iff {F : M → E7}
    (hF : SmoothImmersion F) (x : M) (v : TangentSpace I6 x) :
    inducedMetric F x v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    exact (ne_of_gt (hF.inducedMetric_pos x v hv)) h
  · rintro rfl
    simp [inducedMetric]

lemma secondFundamentalBilinear_apply (F ν : M → E7) (x : M)
    (v w : TangentSpace I6 x) :
    secondFundamentalBilinear F ν x v w = secondFundamentalForm F ν x v w := rfl

lemma secondFundamentalForm_add_left (F ν : M → E7) (x : M)
    (u v w : TangentSpace I6 x) :
    secondFundamentalForm F ν x (u + v) w =
      secondFundamentalForm F ν x u w + secondFundamentalForm F ν x v w := by
  simp [secondFundamentalForm, inner_add_left, add_comm]

lemma secondFundamentalForm_smul_left (F ν : M → E7) (x : M)
    (c : ℝ) (v w : TangentSpace I6 x) :
    secondFundamentalForm F ν x (c • v) w =
      c * secondFundamentalForm F ν x v w := by
  simp [secondFundamentalForm, inner_smul_left]

lemma GlobalUnitNormal.normal_ne_zero {F ν : M → E7} (hν : GlobalUnitNormal F ν)
    (x : M) : ν x ≠ 0 := by
  intro h
  have := hν.unit x
  simp [h] at this

lemma secondFundamentalForm_eq_zero_of_normal_derivative_eq_zero
    (F ν : M → E7) (x : M) (h : differential ν x = 0)
    (v w : TangentSpace I6 x) : secondFundamentalForm F ν x v w = 0 := by
  simp [secondFundamentalForm, h]

lemma SmoothImmersion.toRiemannianMetric_inner [IsManifold I6 ∞ M]
    {F : M → E7} (hF : SmoothImmersion F) (x : M) (v w : TangentSpace I6 x) :
    hF.toRiemannianMetric.inner x v w = inducedMetric F x v w := rfl

end StableBernstein.W01

end

end OAI
