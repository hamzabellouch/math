import Mathlib
import OAI.Analysis.AffineBernstein.AffineParametricStationarity
import OAI.Analysis.AffineBernstein.ParametricDensityCoordinates
import OAI.Analysis.AffineBernstein.ParametricSmoothness

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma variationConormal_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (g d : ι → ℝ) (t : ℝ) (hJ : (1 + t • D).det ≠ 0) (j : ι) :
    (∑ k, variationConormal D g d t k * (1 + t • D) k j) = g j + t * d j := by
  have hh := Matrix.vecMul_vecMul (fun k => g k + t * d k)
    (1 + t • D)⁻¹ (1 + t • D)
  rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hJ), Matrix.vecMul_one] at hh
  exact congrFun hh j

lemma graphParamConormal_null {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u x)
    (hβ : DifferentiableAt ℝ β x) (ha : ∀ k, DifferentiableAt ℝ (a k) x) (t : ℝ)
    (hJ : (1 + t • horizontalJacobian a x).det ≠ 0) :
    (graphParamConormal u β a x t).comp (fderiv ℝ (graphParamVariation u β a t) x) = 0 := by
  have hv (j : Fin n) : graphParamConormal u β a x t
      (fderiv ℝ (graphParamVariation u β a t) x (coordinateVector n j)) = 0 := by
    rw [graphParamVariation_fderiv hu hβ ha, graphParamConormal_apply]
    have he (k : Fin n) :
        (coordinateVector n j + t • (EuclideanSpace.equiv (Fin n) ℝ).symm
          (fun k => dirDeriv (coordinateVector n j) (a k) x)) k =
        (1 + t • horizontalJacobian a x) k j := by
      simp [coordinateVector, horizontalJacobian, Matrix.one_apply, eq_comm]
    simp_rw [he]
    rw [variationConormal_mul _ _ _ _ hJ, sub_self]
  apply ContinuousLinearMap.ext
  intro z
  rw [← sum_coordinateVector z]
  simp only [ContinuousLinearMap.comp_apply, map_sum, map_smul, hv, smul_zero,
    Finset.sum_const_zero, zero_apply]

lemma contDiffAt_graphParamVariation {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {x : Space n} (hu : ContDiffAt ℝ ∞ u x)
    (hβ : ContDiffAt ℝ ∞ β x) (ha : ∀ k, ContDiffAt ℝ ∞ (a k) x) (t : ℝ) :
    ContDiffAt ℝ ∞ (graphParamVariation u β a t) x := by
  have hh : ContDiffAt ℝ ∞ (horizontalVelocity a) x :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.contDiffAt.comp x (contDiffAt_pi.mpr ha)
  exact (contDiffAt_id.add (hh.const_smul t)).prodMk (hu.add (contDiffAt_const.mul hβ))

lemma parametricJacobian_det {n : ℕ} (φ : Space n → Space n) (x : Space n) :
    (parametricJacobian φ x).det = LinearMap.det (fderiv ℝ φ x).toLinearMap := by
  have he : parametricJacobian φ x = LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (fderiv ℝ φ x).toLinearMap := by
    ext i j
    rfl
  rw [he, LinearMap.det_toMatrix]

lemma eventually_uniform_compact_zero {E : Type*} [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K) {P : ℝ × E → Prop}
    (hP : ∀ x ∈ K, {q | P q} ∈ nhds (0,x)) :
    ∀ᶠ t : ℝ in nhds 0, ∀ x ∈ K, P (t,x) := by
  have hs : {0} ×ˢ K ⊆ interior {q | P q} := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    simp only [mem_singleton_iff] at ht
    subst t
    exact mem_interior_iff_mem_nhds.mpr (hP x hx)
  obtain ⟨V,W,hV,hW,h0V,hKW,hVW⟩ := generalized_tube_lemma isCompact_singleton hK isOpen_interior hs
  filter_upwards [hV.mem_nhds (h0V (by simp))] with t ht
  intro x hx
  exact interior_subset (hVW ⟨ht,hKW hx⟩)

lemma eventually_graphVariation_positive {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef) :
    ∀ᶠ t : ℝ in nhds 0, ∀ x ∈ K,
      (graphVariationJacobian a (t,x)).det ≠ 0 ∧ 0 < (graphVariationSecond u β a (t,x)).det := by
  apply eventually_uniform_compact_zero hK (P := fun q =>
    (graphVariationJacobian a q).det ≠ 0 ∧ 0 < (graphVariationSecond u β a q).det)
  intro x hx
  have huc := hu.contDiffAt (hΩ.mem_nhds (hKΩ hx))
  have hβc := hβ.contDiffAt (hΩ.mem_nhds (hKΩ hx))
  have hac (k : Fin n) := (ha k).contDiffAt (hΩ.mem_nhds (hKΩ hx))
  have hJ0 : (graphVariationJacobian a (0,x)).det ≠ 0 := by simp [graphVariationJacobian]
  have hH0 : 0 < (graphVariationSecond u β a (0,x)).det := by
    simpa [graphVariationSecond] using (hp x (hKΩ hx)).det_pos
  have hJ := ((continuousDetRows (ι := Fin n)).contDiff.contDiffAt.comp (0,x)
    (contDiffAt_graphVariationJacobian hac)).continuousAt.eventually_ne hJ0
  have hH := ((continuousDetRows (ι := Fin n)).contDiff.contDiffAt.comp (0,x)
    (contDiffAt_graphVariationSecond huc hβc hac hJ0)).continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds hH0)
  filter_upwards [hJ,hH] with q hq1 hq2
  exact ⟨hq1,hq2⟩

def coordinateAffineVariationArea {n : ℕ} (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    (v : Space n × ℝ) (φ : Space n → Space n) (u β : Space n → ℝ)
    (a : Fin n → Space n → ℝ) (x : Space n) (t : ℝ) : ℝ :=
  parametricAreaDensity (graphAmbientBasis n)
    ((fun y => L (graphParamVariation u β a t y) + v) ∘ φ)
    ((graphParamConormal u β a (φ x) t).comp L.symm.toContinuousLinearMap)
    (L ((0 : Space n),1)) x

lemma coordinateAffineVariationArea_eq {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {φ : Space n → Space n} {x : Space n} (hφ : ContDiffAt ℝ ∞ φ x)
    (hx : φ x ∈ Ω) (hφJ : (parametricJacobian φ x).det ≠ 0) (t : ℝ)
    (hJ : (graphVariationJacobian a (t,φ x)).det ≠ 0)
    (hH : 0 ≤ (graphVariationSecond u β a (t,φ x)).det) :
    coordinateAffineVariationArea L v φ u β a x t =
      |LinearMap.det (fderiv ℝ φ x).toLinearMap| * affineParametricVariationArea L v u β a (φ x) t := by
  have huc := hu.contDiffAt (hΩ.mem_nhds hx)
  have hβc := hβ.contDiffAt (hΩ.mem_nhds hx)
  have hac (k : Fin n) := (ha k).contDiffAt (hΩ.mem_nhds hx)
  have hX := contDiffAt_graphParamVariation huc hβc hac t
  have hXL : ContDiffAt ℝ ∞ (fun y => L (graphParamVariation u β a t y) + v) (φ x) :=
    (L.contDiff.contDiffAt.comp (φ x) hX).add contDiffAt_const
  have hν := graphParamConormal_null (huc.differentiableAt (by simp))
    (hβc.differentiableAt (by simp)) (fun k => (hac k).differentiableAt (by simp)) t hJ
  have hn : ((graphParamConormal u β a (φ x) t).comp L.symm.toContinuousLinearMap).comp
      (fderiv ℝ (fun y => L (graphParamVariation u β a t y) + v) (φ x)) = 0 := by
    have hd := ((L.hasFDerivAt.comp (φ x) (hX.differentiableAt (by simp)).hasFDerivAt).add_const v).fderiv
    have hd' : fderiv ℝ (fun y => L (graphParamVariation u β a t y) + v) (φ x) =
        L.toContinuousLinearMap.comp (fderiv ℝ (graphParamVariation u β a t) (φ x)) := by
      convert! hd using 1
    rw [hd']
    ext z
    have hh := congrArg (fun A : Space n →L[ℝ] ℝ => A z) hν
    simpa using hh
  have hHH : 0 ≤ (parametricSecondForm (fun y => L (graphParamVariation u β a t y) + v)
      ((graphParamConormal u β a (φ x) t).comp L.symm.toContinuousLinearMap) (φ x)).det := by
    rw [parametricSecondForm_affine, graphParam_secondForm hΩ hu hβ ha hx]
    exact hH
  unfold coordinateAffineVariationArea
  rw [parametricAreaDensity_comp _ hXL hφ _ _ hn hHH hφJ, parametricJacobian_det]
  rfl

end AffineBernstein
end

end OAI
