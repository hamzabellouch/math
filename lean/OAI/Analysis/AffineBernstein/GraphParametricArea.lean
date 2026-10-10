import Mathlib
import OAI.Analysis.AffineBernstein.ConvexSmoothMax
import OAI.Analysis.AffineBernstein.CapChangeOfVariables
import OAI.Analysis.AffineBernstein.ParametricGraphJets
import OAI.Analysis.AffineBernstein.ParametricAffineArea

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def horizontalVelocity {n : ℕ} (a : Fin n → Space n → ℝ) (x : Space n) : Space n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => a i x)

def graphParamVariation {n : ℕ} (u β : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (t : ℝ) (x : Space n) : Space n × ℝ :=
  (x + t • horizontalVelocity a x, u x + t * β x)

def graphParamConormal {n : ℕ} (u β : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (x : Space n) (t : ℝ) : (Space n × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ (Space n) ℝ - ∑ k,
    variationConormal (horizontalJacobian a x)
      (fun k => dirDeriv (coordinateVector n k) u x)
      (fun k => dirDeriv (coordinateVector n k) β x) t k •
      ((coordinateProjection n k).comp (ContinuousLinearMap.fst ℝ (Space n) ℝ))

@[simp] lemma graphParamConormal_apply {n : ℕ} (u β : Space n → ℝ)
    (a : Fin n → Space n → ℝ) (x : Space n) (t : ℝ) (z : Space n × ℝ) :
    graphParamConormal u β a x t z = z.2 - ∑ k,
      variationConormal (horizontalJacobian a x)
        (fun k => dirDeriv (coordinateVector n k) u x)
        (fun k => dirDeriv (coordinateVector n k) β x) t k * z.1 k := by
  simp [graphParamConormal]

@[simp] lemma graphParamConormal_vertical {n : ℕ} (u β : Space n → ℝ)
    (a : Fin n → Space n → ℝ) (x : Space n) (t : ℝ) :
    graphParamConormal u β a x t ((0 : Space n), 1) = 1 := by simp

lemma differentiableAt_horizontalVelocity {n : ℕ} {a : Fin n → Space n → ℝ}
    {x : Space n} (ha : ∀ k, DifferentiableAt ℝ (a k) x) :
    DifferentiableAt ℝ (horizontalVelocity a) x :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.differentiableAt.comp x (differentiableAt_pi.mpr ha)

lemma differentiableAt_graphParamVariation {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u x)
    (hβ : DifferentiableAt ℝ β x) (ha : ∀ k, DifferentiableAt ℝ (a k) x) (t : ℝ) :
    DifferentiableAt ℝ (graphParamVariation u β a t) x :=
  (differentiableAt_id.add ((differentiableAt_horizontalVelocity ha).const_smul t)).prodMk
    (hu.add (hβ.const_mul t))

lemma graphParamVariation_fderiv {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u x)
    (hβ : DifferentiableAt ℝ β x) (ha : ∀ k, DifferentiableAt ℝ (a k) x) (t : ℝ) (j : Fin n) :
    fderiv ℝ (graphParamVariation u β a t) x (coordinateVector n j) =
      (coordinateVector n j + t • (EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun k => dirDeriv (coordinateVector n j) (a k) x),
       dirDeriv (coordinateVector n j) u x + t * dirDeriv (coordinateVector n j) β x) := by
  have hv := (EuclideanSpace.equiv (Fin n) ℝ).symm.hasFDerivAt.comp x
    (hasFDerivAt_pi.mpr (fun k => (ha k).hasFDerivAt))
  have hh := ((hasFDerivAt_id x).add (hv.const_smul t)).prodMk
    (hu.hasFDerivAt.add (hβ.hasFDerivAt.const_mul t))
  convert! congrArg (fun T : Space n →L[ℝ] (Space n × ℝ) => T (coordinateVector n j)) hh.fderiv using 1

lemma graphParam_frame_determinant {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u x)
    (hβ : DifferentiableAt ℝ β x) (ha : ∀ k, DifferentiableAt ℝ (a k) x) (t : ℝ) :
    (graphAmbientBasis n).det (parametricFrame (graphParamVariation u β a t) ((0 : Space n), 1) x) =
      (1 + t • horizontalJacobian a x).det := by
  rw [Module.Basis.det_apply]
  have he : (graphAmbientBasis n).toMatrix
      (parametricFrame (graphParamVariation u β a t) ((0 : Space n), 1) x) =
      Matrix.fromBlocks (1 + t • horizontalJacobian a x) 0
        (Matrix.of fun (_ : Unit) j => dirDeriv (coordinateVector n j) u x +
          t * dirDeriv (coordinateVector n j) β x) (1 : Matrix Unit Unit ℝ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [Module.Basis.toMatrix_apply, graphAmbientBasis, parametricFrame,
        Sum.elim_inl, Module.Basis.prod_repr_inl]
      rw [graphParamVariation_fderiv hu hβ ha]
      simp [coordinateVector, Matrix.fromBlocks, Matrix.one_apply, horizontalJacobian]
    · simp [Module.Basis.toMatrix_apply, graphAmbientBasis, parametricFrame, Matrix.fromBlocks]
    · simp [Module.Basis.toMatrix_apply, graphAmbientBasis, parametricFrame,
        graphParamVariation_fderiv hu hβ ha, Matrix.fromBlocks]
    · simp [Module.Basis.toMatrix_apply, graphAmbientBasis, parametricFrame, Matrix.fromBlocks]
  rw [he, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

lemma hessian_coordinate {n : ℕ} (k : Fin n) (x : Space n) :
    hessian (fun y : Space n => y k) x = 0 := by
  change hessian (coordinateProjection n k) x = 0
  ext i j
  simp [hessian, (coordinateProjection n k).fderiv]

lemma graphParam_secondForm {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω) {x : Space n} (hx : x ∈ Ω) (t : ℝ) :
    parametricSecondForm (graphParamVariation u β a t) (graphParamConormal u β a x t) x =
      variationSecondForm (hessian u x) (hessian β x) (horizontalJacobian a x)
        (fun k => dirDeriv (coordinateVector n k) u x)
        (fun k => dirDeriv (coordinateVector n k) β x)
        (fun k => hessian (a k) x) t := by
  let q := variationConormal (horizontalJacobian a x)
    (fun k => dirDeriv (coordinateVector n k) u x)
    (fun k => dirDeriv (coordinateVector n k) β x) t
  have he : (fun y => graphParamConormal u β a x t (graphParamVariation u β a t y)) =
      fun y => u y + t * β y - ∑ k, q k * (y k + t * a k y) := by
    funext y
    simp [graphParamVariation, horizontalVelocity, q]
  have hcoord (k : Fin n) : ContDiffOn ℝ ∞ (fun y : Space n => y k) Ω :=
    (coordinateProjection n k).contDiff.contDiffOn
  have hc (k : Fin n) : ContDiffOn ℝ ∞ (fun y : Space n => y k + t * a k y) Ω :=
    (hcoord k).add (contDiffOn_const.mul (ha k))
  unfold parametricSecondForm
  rw [he, hessian_sub_on hΩ (hu.add (contDiffOn_const.mul hβ))
    (ContDiffOn.sum (fun k _ => contDiffOn_const.mul (hc k))) hx,
    hessian_add_on hΩ hu (contDiffOn_const.mul hβ) hx, hessian_const_mul hΩ hβ t hx]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    hessian_sum_on hΩ (fun k => contDiffOn_const.mul (hc k)) hx,
    hessian_const_mul hΩ (hc _) _ hx,
    hessian_add_on hΩ (hcoord _) (contDiffOn_const.mul (ha _)) hx,
    hessian_const_mul hΩ (ha _) t hx, hessian_coordinate, zero_add,
    variationSecondForm, Matrix.of_apply, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/- The abstract conormal formula is exactly the literal graph-variation density. -/
theorem parametricAreaDensity_graphVariation {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω) {x : Space n} (hx : x ∈ Ω) (t : ℝ) :
    parametricAreaDensity (graphAmbientBasis n) (graphParamVariation u β a t)
      (graphParamConormal u β a x t) ((0 : Space n), 1) x = graphVariationArea u β a x t := by
  rw [parametricAreaDensity, graphParam_secondForm hΩ hu hβ ha hx,
    graphParam_frame_determinant (hu.differentiableOn (by simp) x hx |>.differentiableAt (hΩ.mem_nhds hx))
      (hβ.differentiableOn (by simp) x hx |>.differentiableAt (hΩ.mem_nhds hx))
      (fun k => (ha k).differentiableOn (by simp) x hx |>.differentiableAt (hΩ.mem_nhds hx))]
  unfold graphVariationArea variationAreaDensity
  simp [div_eq_mul_inv]

end AffineBernstein
end

end OAI
