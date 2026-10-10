import Mathlib
import OAI.Analysis.AffineBernstein.NormalizedHessianUpper
import OAI.Analysis.AffineBernstein.MatrixUniformBounds

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section GlobalHessianBound
open Matrix

lemma second_directional_eq_quadratic {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (e x : Space n) :
    dirDeriv e (dirDeriv e u) x = (fun i => e i) ⬝ᵥ ((hessian u x)*ᵥ (fun i => e i)) := by
  rw [dirDeriv_eq_second hu.contDiffAt,second_fderiv_eq_sum hu.contDiffAt]
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

lemma second_directional_normalized {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) (e x : Space n) :
    dirDeriv e (dirDeriv e (normalizedFunction u A t)) x =
      t⁻¹*dirDeriv (A e) (dirDeriv (A e) u) (A x) := by
  change dirDeriv e (dirDeriv e (fun y => t⁻¹*u (A y))) x = _
  rw [second_dirDeriv_const_mul isOpen_univ (contDiff_comp_cle hu A).contDiffOn
    (mem_univ x),dirDeriv_eq_second (contDiff_comp_cle hu A).contDiffAt,
    dirDeriv_eq_second hu.contDiffAt]
  have H := second_fderiv_affine_comp A.toContinuousLinearMap (0:Space n) (x := x) hu.contDiffAt e e
  simpa only [zero_add,ContinuousLinearEquiv.coe_coe] using congrArg (fun z : ℝ => t⁻¹*z) H

/-- The pointwise normalized estimate transfers through actual section maps
to a global upper bound for every directional second derivative. -/
theorem centered_balanced_global_directional_bound {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) (hzero : u 0=0) (hdzero : fderiv ℝ u 0=0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ e x : Space n,
      dirDeriv e (dirDeriv e u) x ≤ C*dirDeriv e (dirDeriv e u) 0 := by
  classical
  obtain ⟨R,hR,Hnorm⟩ := centered_normalization_at_points hn hu hp hm hzero hdzero hρ hρ1 hbal
  obtain ⟨c,D,hc,hD,Hdet⟩ := normalized_balanced_det_bounds hρ hρ1 hR (n := n)
  obtain ⟨C,hC,Htr⟩ := normalized_hessian_trace_upper hn hρ hρ1 hR
  let d := c/(C+1)^n
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨C/d,div_pos hC hd,?_⟩
  intro e x
  obtain ⟨t,ht,A,hv,Hpts⟩ := Hnorm {0,x}
  let v := normalizedFunction u A t
  let p := A.symm e
  have h0 : (0:Space n) ∈ Metric.ball 0 (1/64:ℝ) := by simp
  have hx : A.symm x ∈ Metric.ball (0:Space n) (1/64:ℝ) := Hpts x (by simp)
  have h0det : c ≤ (hessian v 0).det := (Hdet v hv.smooth hv.posDef hv.maximal hv.zero hv.deriv_zero
    hv.balance hv.inner hv.outer 0 (by simp)).1
  have hlo := (posDef_quadratic_bounds (hv.posDef 0) hc hC.le h0det (Htr v hv 0 h0)
    (fun i => p i)).1
  have hhi := (posSemidef_quadratic_le_trace_mul_sq (hv.posDef (A.symm x)).posSemidef (fun i => p i)).trans
    (mul_le_mul_of_nonneg_right (Htr v hv (A.symm x) hx)
      (Finset.sum_nonneg fun index _ => sq_nonneg (p index)))
  rw [← second_directional_eq_quadratic hv.smooth,second_directional_normalized hu] at hlo hhi
  simp only [p,ContinuousLinearEquiv.apply_symm_apply,map_zero] at hlo hhi
  change d*(∑ i, (p i)^2) ≤ t⁻¹*dirDeriv e (dirDeriv e u) 0 at hlo
  have Hscaled := mul_le_mul_of_nonneg_left hlo (div_pos hC hd).le
  have he : (C/d)*(d*(∑ i, (p i)^2)) = C*(∑ i, (p i)^2) := by field_simp
  rw [he] at Hscaled
  have H := hhi.trans Hscaled
  apply (mul_le_mul_iff_right₀ (inv_pos.mpr ht)).mp
  nlinarith [H]

theorem balanced_global_directional_bddAbove {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hbal : SectionBalance univ u ρ) (e : Space n) :
    BddAbove (range (dirDeriv e (dirDeriv e u))) := by
  let v := tangentShift u 0 0
  have hv : ContDiff ℝ ∞ v := contDiffOn_univ.mp (contDiffOn_tangentShift hu.contDiffOn 0 0)
  have hh (x : Space n) : hessian v x = hessian u x := hessian_tangentShift isOpen_univ hu.contDiffOn 0 0 (mem_univ x)
  have hvp (x : Space n) : (hessian v x).PosDef := hh x ▸ hp x
  have hvm := affineMaximalOn_tangentShift isOpen_univ hu.contDiffOn hm 0 0
  have hv0 : v 0=0 := by simp [v,tangentShift,tangentHeight]
  have hdv0 : fderiv ℝ v 0=0 := by
    dsimp [v]
    rw [fderiv_tangentShift (hu.differentiable (by simp) 0)]
    exact sub_self _
  obtain ⟨C,hC,HC⟩ := centered_balanced_global_directional_bound hn hv hvp hvm hv0 hdv0 hρ hρ1
    (sectionBalance_tangentShift hu hbal 0 0)
  have he (x : Space n) : dirDeriv e (dirDeriv e v) x = dirDeriv e (dirDeriv e u) x := by
    rw [second_directional_eq_quadratic hv,second_directional_eq_quadratic hu,hh]
  refine ⟨C*dirDeriv e (dirDeriv e u) 0,?_⟩
  rintro y ⟨x,rfl⟩
  simpa only [he] using HC e x

end GlobalHessianBound


end
end AffineBernstein
end

end OAI
