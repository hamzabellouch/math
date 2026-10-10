import Mathlib
import OAI.Analysis.AffineBernstein.CapPerturbation
import OAI.Analysis.AffineBernstein.TriangularGraph
import OAI.Analysis.AffineBernstein.CapChangeOfVariables

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section CapCovariance

lemma affine_area_scaling_identity (n : ℕ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    Real.rpow (c^n*d^2) (1/((n:ℝ)+2)) =
      d*Real.rpow (c/d) ((n:ℝ)/((n:ℝ)+2)) := by
  have hn : (n:ℝ)+2 ≠ 0 := by positivity
  have hfrac : (n:ℝ)*(1/((n:ℝ)+2)) = (n:ℝ)/((n:ℝ)+2) := by ring
  have hsum : (n:ℝ)/((n:ℝ)+2)+2*(1/((n:ℝ)+2)) = 1 := by field_simp
  have hh := Real.rpow_add hd ((n:ℝ)/((n:ℝ)+2)) (2*(1/((n:ℝ)+2)))
  rw [hsum,Real.rpow_one] at hh
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (pow_nonneg hc.le _) (sq_nonneg _),
    ← Real.rpow_natCast_mul hc.le n, ← Real.rpow_natCast_mul hd.le 2,hfrac,
    Real.div_rpow hc.le hd.le]
  have hdne : Real.rpow d ((n:ℝ)/((n:ℝ)+2)) ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
  apply (mul_right_cancel₀ hdne)
  field_simp
  norm_num only [Nat.cast_ofNat] at *
  rw [show (2:ℝ)*(1/((n:ℝ)+2)) = 2/((n:ℝ)+2) by ring] at hh
  nlinarith [hh]

/-- Affine area of the actual cap, in the original global graph chart.
The determinant exponent is the one proved for the literal parametric density. -/
def affineImageCapArea {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) (b : ℝ) : ℝ :=
  Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
    ∫ x in {x | x ∈ Ω ∧ (L (x,u x)+v).2 < b}, affineAreaDensity u x

lemma triangular_area_scaling {n : ℕ} (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    {c : ℝ} (hc : M (0,1) = (0,c)) (hcp : 0 < c) :
    Real.rpow (c^n*(equivMatrix (triangularBaseEquiv M hc hcp.ne').symm).det^2)
        (1/((n:ℝ)+2)) =
      |(equivMatrix (triangularBaseEquiv M hc hcp.ne').symm).det| *
        Real.rpow |M.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) := by
  let P := triangularBaseEquiv M hc hcp.ne'
  have hid : |P.toContinuousLinearMap.det| * |P.symm.toContinuousLinearMap.det| = 1 := by
    rw [← abs_mul]
    have hi := P.toLinearEquiv.det_mul_det_symm
    change P.toContinuousLinearMap.det*P.symm.toContinuousLinearMap.det = 1 at hi
    rw [hi,abs_one]
  have hpos : 0 < |(equivMatrix P.symm).det| := abs_pos.mpr (equivMatrix_det_ne _)
  have hdiv : c/|(equivMatrix P.symm).det| = |M.toContinuousLinearMap.det| := by
    apply (div_eq_iff hpos.ne').mpr
    rw [equivMatrix_det,determinant_triangular M hc hcp.ne',abs_mul,abs_of_pos hcp]
    change c = (|P.toContinuousLinearMap.det| * c) * |P.symm.toContinuousLinearMap.det|
    calc
      _ = c*1 := (mul_one c).symm
      _ = _ := by rw [← hid]; ring
  change Real.rpow (c^n*(equivMatrix P.symm).det^2) _ = _
  rw [← sq_abs (equivMatrix P.symm).det,affine_area_scaling_identity n hcp hpos,hdiv]

/-- The true cap integral is identical in the sheared graph coordinates. -/
theorem triangular_graph_cap_area {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcp : 0 < c) (v : Space n × ℝ) (b : ℝ) :
    (∫ y in {y | (triangularBaseEquiv M hc hcp.ne').symm (y-v.1) ∈ Ω ∧
        triangularGraphFunction u M hc hcp.ne' v y < b},
       affineAreaDensity (triangularGraphFunction u M hc hcp.ne' v) y) =
      affineImageCapArea Ω u M v b := by
  let P := triangularBaseEquiv M hc hcp.ne'
  let a := (triangularLinearHeight M).comp P.symm.toContinuousLinearMap
  let E : Set (Space n) := {x | x ∈ Ω ∧ (M (x,u x)+v).2 < b}
  have hE : MeasurableSet E := by
    apply IsOpen.measurableSet
    exact isOpen_graphSublevel hΩ
      (continuous_snd.comp_continuousOn
        ((M.continuous.comp_continuousOn (continuousOn_id.prodMk hu.continuousOn)).add_const v)) b
  have he (y : Space n) : (M ((P.symm y-P.symm v.1),u (P.symm y-P.symm v.1))+v).2 =
      triangularGraphFunction u M hc hcp.ne' v y := by
    rw [triangularGraphFunction_eval]
    change (M (_, _)).2+v.2 = _
    rw [triangular_snd M hc,map_sub]
    rfl
  have hset : {y | P.symm y+(-P.symm v.1) ∈ E} =
      {y | P.symm (y-v.1) ∈ Ω ∧ triangularGraphFunction u M hc hcp.ne' v y < b} := by
    ext y
    simp only [E,mem_ofPred_eq,sub_eq_add_neg,map_add,map_neg] at he ⊢
    rw [← he]
  have hi := affine_area_pullback_integral hΩ hu hp hE (fun x hx => hx.1)
    P.symm (-P.symm v.1) a hcp (v.2-a v.1)
  change |(equivMatrix P.symm).det| * (∫ y in {y | P.symm y+(-P.symm v.1) ∈ E},
      affineAreaDensity (triangularGraphFunction u M hc hcp.ne' v) y) = _ at hi
  rw [hset,triangular_area_scaling M hc hcp] at hi
  apply mul_left_cancel₀ (abs_pos.mpr (equivMatrix_det_ne P.symm)).ne'
  exact hi.trans (by simp only [affineImageCapArea,E,P,mul_assoc])

lemma affineImageCapArea_shear {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) (b : ℝ)
    (p : Space n) :
    affineImageCapArea Ω u (L.trans (verticalShear p)) (verticalShear p v) b =
      affineImageCapArea Ω u L v b := by
  have hd : (L.trans (verticalShear p)).toContinuousLinearMap.det = L.toContinuousLinearMap.det := by
    change LinearMap.det ((verticalShear p).toLinearEquiv.toLinearMap.comp L.toLinearEquiv.toLinearMap) = _
    rw [LinearMap.det_comp]
    change (verticalShear p).toContinuousLinearMap.det*L.toContinuousLinearMap.det = _
    rw [det_verticalShear,one_mul]
  simp only [affineImageCapArea,hd,ContinuousLinearEquiv.trans_apply,verticalShear_apply,
    Prod.snd_add]

end CapCovariance
theorem hessian_eq_second {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    hessian u x i j =
      fderiv ℝ (fderiv ℝ u) x (coordinateVector n i) (coordinateVector n j) := by
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const (coordinateVector n j) x)
  unfold hessian
  rw [he.fderiv]
  simp

theorem second_fderiv_eq_sum {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (v : Space n) :
    fderiv ℝ (fderiv ℝ u) x v v =
    ∑ i, ∑ j, v i * hessian u x i j * v j := by
  calc
    _ = fderiv ℝ (fderiv ℝ u) x (∑ i, v i • coordinateVector n i)
        (∑ j, v j • coordinateVector n j) := by rw [sum_coordinateVector]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hessian_eq_second hu,
        hu.isSymmSndFDerivAt (by simp)
          (coordinateVector n j) (coordinateVector n i)]
      ring

theorem second_fderiv_nonneg {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosSemidef) (v : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ u) x v v := by
  rw [second_fderiv_eq_sum hu]
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hp.dotProduct_mulVec_nonneg (fun i => v i)

theorem second_fderiv_pos {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) {v : Space n} (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ u) x v v := by
  rw [second_fderiv_eq_sum hu]
  have hv' : (fun i => v i) ≠ 0 := fun he => hv (by ext i; exact congrFun he i)
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hp.dotProduct_mulVec_pos hv'

end AffineBernstein
end

end OAI
