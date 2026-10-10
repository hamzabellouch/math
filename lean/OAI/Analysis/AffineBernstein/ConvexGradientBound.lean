import Mathlib
import OAI.Analysis.AffineBernstein.DeterminantVariation
import OAI.Analysis.AffineBernstein.GraphAreaCharts

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section ConvexGradientBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convex_fderiv_support {Ω : Set E} {f : E → ℝ} (hc : ConvexOn ℝ Ω f)
    {x y : E} (hx : x ∈ Ω) (hy : y ∈ Ω) (hd : DifferentiableAt ℝ f x) :
    fderiv ℝ f x (y-x) ≤ f y-f x := by
  have hh := hc.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)
  have hγ : HasDerivAt (fun t : ℝ => t • (y-x)+x) (y-x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y-x)).add_const x
  have hdf : HasDerivAt (f ∘ AffineMap.lineMap (k := ℝ) x y) (fderiv ℝ f x (y-x)) 0 := by
    have hd' : HasFDerivAt f (fderiv ℝ f x) ((0:ℝ) • (y-x)+x) := by
      simpa using hd.hasFDerivAt
    simpa only [AffineMap.lineMap_apply_module',Function.comp_def] using
      hd'.comp_hasDerivAt 0 hγ
  have h0 : (0:ℝ) ∈ AffineMap.lineMap (k := ℝ) x y ⁻¹' Ω := by simpa
  have h1 : (1:ℝ) ∈ AffineMap.lineMap (k := ℝ) x y ⁻¹' Ω := by simpa
  have hs := hh.le_slope_of_hasDerivAt h0 h1 (by norm_num) hdf
  simpa only [slope_def_field,sub_zero,div_one,Function.comp_apply,
    AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] using hs

end ConvexGradientBound
section GraphProjection
variable {n : ℕ}

lemma norm_le_card_of_coord_bound {p : Space n} {R : ℝ}
    (_hR : 0 ≤ R) (hp : ∀ i, |p i| ≤ R) : ‖p‖ ≤ n*R := by
  rw [← sum_coordinateVector p]
  calc
    _ ≤ ∑ i, ‖p i • coordinateVector n i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, R := by
      apply Finset.sum_le_sum
      intro i _
      simpa [norm_smul,coordinateVector,Real.norm_eq_abs] using hp i
    _ = _ := by simp

/-- Projection to the coordinate hyperplane omitting the i-th original
base coordinate, represented in its standard n coordinates. -/
def graphProjection (u : Space n → ℝ) (i : Fin n) (x : Space n) : Space n :=
  WithLp.toLp 2 (Function.update (fun j => x j) i (u x))

lemma contDiffAt_graphProjection {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i : Fin n) :
    ContDiffAt ℝ ∞ (graphProjection u i) x := by
  apply (contDiffAt_piLp 2).mpr
  intro j
  by_cases hj : j=i
  · simpa [graphProjection,hj] using hu
  · simpa [graphProjection,hj] using (EuclideanSpace.proj j : Space n →L[ℝ] ℝ).contDiff.contDiffAt

lemma det_fderiv_graphProjection {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i : Fin n) :
    (fderiv ℝ (graphProjection u i) x).det = gradient u x i := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hm : LinearMap.toMatrix b b (fderiv ℝ (graphProjection u i) x).toLinearMap =
      (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i (fun j => gradient u x j) := by
    ext j k
    rw [toMatrix_fderiv_euclidean ((contDiffAt_graphProjection hu i).differentiableAt (by simp))]
    by_cases hj : j=i
    · subst j
      simp only [graphProjection,WithLp.ofLp_toLp,Function.update_self,Matrix.updateRow_self]
      change fderiv ℝ u x (coordinateVector n k) = _
      rw [← inner_gradient_left]
      simp only [coordinateVector,EuclideanSpace.inner_single_right,
        RCLike.conj_to_real,one_mul]
    · simp only [graphProjection,WithLp.ofLp_toLp,Function.update_of_ne hj,
        Matrix.updateRow_ne hj]
      change fderiv ℝ (EuclideanSpace.proj j : Space n →L[ℝ] ℝ) x (coordinateVector n k) = _
      rw [ContinuousLinearMap.fderiv]
      simp [coordinateVector,Matrix.one_apply]
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix b,hm,← Matrix.det_transpose]
  rw [← Matrix.updateCol_transpose,Matrix.transpose_one]
  exact det_updateCol_identity i (fun j => gradient u x j)

lemma graphProjection_difference {u : Space n → ℝ} (i : Fin n) {x y : Space n}
    (he : graphProjection u i x = graphProjection u i y) :
    y-x = (y i-x i) • coordinateVector n i ∧ u x = u y := by
  have hh (j : Fin n) := congrArg (fun z : Space n => z j) he
  have heq : u x=u y := by simpa [graphProjection] using hh i
  refine ⟨?_,heq⟩
  ext j
  by_cases hj : j=i
  · subst j
    simp [coordinateVector]
  · have hxy : x j=y j := by simpa [graphProjection,hj] using hh j
    simp [coordinateVector,hj,hxy]

lemma graphProjection_injOn_signed {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : ConvexOn ℝ Ω u) (hu : ∀ x ∈ Ω, DifferentiableAt ℝ u x)
    (i : Fin n) {K : Set (Space n)} (hKΩ : K ⊆ Ω)
    (hs : (∀ x ∈ K, 0 < gradient u x i) ∨ (∀ x ∈ K, gradient u x i < 0)) :
    Set.InjOn (graphProjection u i) K := by
  intro x hx y hy he
  obtain ⟨hd,heq⟩ := graphProjection_difference i he
  have hd' : x-y = (x i-y i) • coordinateVector n i := by
    rw [← neg_sub y x,hd,← neg_smul,neg_sub]
  have hxy := convex_fderiv_support hc (hKΩ hx) (hKΩ hy) (hu x (hKΩ hx))
  have hyx := convex_fderiv_support hc (hKΩ hy) (hKΩ hx) (hu y (hKΩ hy))
  have hemi (z : Space n) : fderiv ℝ u z (coordinateVector n i) = gradient u z i := by
    rw [← inner_gradient_left]
    simp only [coordinateVector,EuclideanSpace.inner_single_right,
      RCLike.conj_to_real,one_mul]
  rw [hd,map_smul,smul_eq_mul,hemi,heq,sub_self] at hxy
  rw [hd',map_smul,smul_eq_mul,hemi,heq,sub_self] at hyx
  have hcoord : x i=y i := by
    rcases hs with hs|hs
    · have hp := hs x hx
      have hq := hs y hy
      nlinarith
    · have hp := hs x hx
      have hq := hs y hy
      nlinarith
  apply sub_eq_zero.mp
  rw [hd',hcoord,sub_self,zero_smul]

lemma reciprocalChart_coord_le_one (i : Fin n) {p : Space n}
    (hi : 1 ≤ |p i|) (hmax : ∀ j, |p j| ≤ |p i|) (j : Fin n) :
    |reciprocalChart i p j| ≤ 1 := by
  have hp : 0 < |p i| := lt_of_lt_of_le zero_lt_one hi
  by_cases hj : j=i
  · subst j
    simp only [reciprocalChart,WithLp.ofLp_toLp,ite_true,abs_inv]
    exact inv_le_one_of_one_le₀ hi
  · simp only [reciprocalChart,WithLp.ofLp_toLp,hj,ite_false,abs_div]
    exact (div_le_one hp).mpr (hmax j)

end GraphProjection

/-- Holder interpolation, with weights rather than reciprocal exponents.
The endpoint masses may be infinite; no hidden integrability premise is used. -/
lemma lintegral_geometric_mean_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f g : X → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x ^ p * g x ^ (1-p) ∂μ) ≤
      (∫⁻ x, f x ∂μ)^p * (∫⁻ x, g x ∂μ)^(1-p) := by
  have hconj : p⁻¹.HolderConjugate (1-p)⁻¹ := by
    apply Real.holderConjugate_iff.mpr
    exact ⟨(one_lt_inv₀ hp).mpr hp1,by simp⟩
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj (hf.pow_const p) (hg.pow_const (1-p))
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp1).ne'
  simpa only [← ENNReal.rpow_mul,mul_inv_cancel₀ hp.ne',mul_inv_cancel₀ hq,
    ENNReal.rpow_one,one_div,inv_inv,Pi.mul_apply] using hh

/-- Real positive densities can be interpolated before or after `ofReal`. -/
lemma lintegral_ofReal_geometric_mean_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f g : X → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfp : ∀ᵐ x ∂μ, 0 ≤ f x) (hgp : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (∫⁻ x, ENNReal.ofReal ((f x)^p * (g x)^(1-p)) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ)^p *
      (∫⁻ x, ENNReal.ofReal (g x) ∂μ)^(1-p) := by
  convert lintegral_geometric_mean_le μ hp hp1 hf.ennreal_ofReal hg.ennreal_ofReal using 1
  apply lintegral_congr_ae
  filter_upwards [hfp,hgp] with x hx hy
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hx _),ENNReal.ofReal_rpow_of_nonneg hx hp.le,
    ENNReal.ofReal_rpow_of_nonneg hy (sub_pos.mpr hp1).le]

end AffineBernstein
end

end OAI
