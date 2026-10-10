import Mathlib
import OAI.Analysis.AffineBernstein.PositiveMatrixTraceBound

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section TangentShiftCalculus
open Filter
open scoped Topology

lemma gradientSquared_eq_norm_fderiv {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    gradientSquared f x = ‖fderiv ℝ f x‖^2 := by
  simpa only [gradientSquared,dirDeriv,euclideanGradientSquare,EuclideanSpace.basisFun_apply,
    coordinateVector] using euclideanGradientSquare_eq_norm f x

lemma affineMaximalOn_add_affine {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {f : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hm : AffineMaximalOn Ω f)
    (L : Space n →L[ℝ] ℝ) (c : ℝ) : AffineMaximalOn Ω (graphAffineFunction f L 1 c) := by
  have he (x : Space n) (hx : x ∈ Ω) : hessian (graphAffineFunction f L 1 c) x = hessian f x := by
    ext i j
    simpa only [one_mul] using hessian_graphAffineFunction hΩ hf hx L 1 c i j
  intro x hx
  have hw : affineWeight (graphAffineFunction f L 1 c) =ᶠ[𝓝 x] affineWeight f := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    simp only [affineWeight,he y hy]
  rw [show cofactorHessian (graphAffineFunction f L 1 c) x = cofactorHessian f x by
    simp only [cofactorHessian,he x hx],hessian_congr_nhds hw]
  exact hm x hx

/-- Subtract the tangent plane and a positive section height; this does not
alter the Hessian, hence preserves the original classical PDE. -/
def tangentShift {n : ℕ} (f : Space n → ℝ) (a : Space n) (h : ℝ) (x : Space n) : ℝ :=
  tangentHeight f a x - h

lemma tangentShift_eq_graphAffineFunction {n : ℕ} (f : Space n → ℝ) (a : Space n) (h : ℝ) :
    tangentShift f a h = graphAffineFunction f (-fderiv ℝ f a) 1
      (-f a + fderiv ℝ f a a - h) := by
  funext x
  simp only [tangentShift,tangentHeight,graphAffineFunction,neg_apply,map_sub,one_mul]
  ring

lemma contDiffOn_tangentShift {n : ℕ} {Ω : Set (Space n)} {f : Space n → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (a : Space n) (h : ℝ) :
    ContDiffOn ℝ ∞ (tangentShift f a h) Ω := by
  exact ((hf.sub contDiffOn_const).sub
    ((fderiv ℝ f a).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn).sub contDiffOn_const

lemma hessian_tangentShift {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {f : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (a : Space n) (h : ℝ)
    {x : Space n} (hx : x ∈ Ω) : hessian (tangentShift f a h) x = hessian f x := by
  rw [tangentShift_eq_graphAffineFunction]
  ext i j
  simpa only [one_mul] using hessian_graphAffineFunction hΩ hf hx (-fderiv ℝ f a) 1
    (-f a + fderiv ℝ f a a - h) i j

lemma affineMaximalOn_tangentShift {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {f : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hm : AffineMaximalOn Ω f) (a : Space n) (h : ℝ) :
    AffineMaximalOn Ω (tangentShift f a h) := by
  rw [tangentShift_eq_graphAffineFunction]
  exact affineMaximalOn_add_affine hΩ hf hm _ _

lemma fderiv_tangentShift {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (a : Space n) (h : ℝ) :
    fderiv ℝ (tangentShift f a h) x = fderiv ℝ f x - fderiv ℝ f a := by
  change fderiv ℝ (fun y => f y - f a - fderiv ℝ f a (y-a) - h) x = _
  have hh := ((hf.hasFDerivAt.sub_const (f a)).sub
    ((fderiv ℝ f a).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a))).sub_const h
  simpa only [tangentShift,tangentHeight,Pi.sub_apply,Function.comp_apply,id_eq,
    ContinuousLinearMap.comp_id] using hh.fderiv

lemma norm_fderiv_le_of_convex_bounded {n : ℕ} {Ω : Set (Space n)} {f : Space n → ℝ}
    (hc : ConvexOn ℝ Ω f) {x : Space n} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ f x)
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hball : Metric.closedBall x r ⊆ Ω) (hb : ∀ y ∈ Ω, |f y| ≤ M) :
    ‖fderiv ℝ f x‖ ≤ 2*M/r := by
  have hh := norm_gradient_le_of_convex_bounded hc hx hd hr hM hball hb
  simpa only [gradient,LinearIsometryEquiv.norm_map] using hh

end TangentShiftCalculus


end
end AffineBernstein
end

end OAI
