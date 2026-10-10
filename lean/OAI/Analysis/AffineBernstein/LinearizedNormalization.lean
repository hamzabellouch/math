import Mathlib
import OAI.Analysis.AffineBernstein.SectionNormalizationFamily
import OAI.Analysis.AffineBernstein.NormalizedLogVariance

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LinearizedNormalization

lemma inverseHessianTrace_eq_matrixTrace {n : ℕ} {u s : Space n → ℝ}
    (hs : ContDiff ℝ ∞ s) (x : Space n) :
    inverseHessianTrace u s x = ((hessian u x)⁻¹*hessian s x).trace := by
  symm
  exact matrix_trace_pair _ _ (hessian_isSymm hs.contDiffAt)

lemma contDiff_comp_cle {n : ℕ} {s : Space n → ℝ} (hs : ContDiff ℝ ∞ s)
    (A : Space n ≃L[ℝ] Space n) : ContDiff ℝ ∞ (fun x => s (A x)) :=
  hs.comp A.contDiff

lemma hessian_comp_cle {n : ℕ} {s : Space n → ℝ} (hs : ContDiff ℝ ∞ s)
    (A : Space n ≃L[ℝ] Space n) (x : Space n) :
    hessian (fun y => s (A y)) x = (cleMatrix A).transpose*hessian s (A x)*cleMatrix A := by
  have H := hessian_comp_affine isOpen_univ hs.contDiffOn (cleMatrix A) 0 (x := x) (mem_univ _)
  simpa only [affineBaseMap,cleMatrix_apply,ContinuousLinearEquiv.coe_coe,add_zero] using H

lemma inverseHessianTrace_normalized_comp {n : ℕ} {u s : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hs : ContDiff ℝ ∞ s) (hp : ∀ x, (hessian u x).PosDef)
    (A : Space n ≃L[ℝ] Space n) {t : ℝ} (ht : 0 < t) (x : Space n) :
    inverseHessianTrace (normalizedFunction u A t) (fun y => s (A y)) x =
      t*inverseHessianTrace u s (A x) := by
  rw [inverseHessianTrace_eq_matrixTrace (contDiff_comp_cle hs A),
    inverseHessianTrace_eq_matrixTrace hs,hessian_normalizedFunction hu,hessian_comp_cle hs]
  have H := trace_inverse_congruence (hp (A x)) (cleMatrix_det_ne_zero A) (inv_pos.mpr ht)
    (hessian s (A x)) 1
  simpa only [one_smul,inv_inv,mul_one] using H

/-- The previously produced normalizations can put any finite collection
of fixed original points in the same small inner ball. -/
theorem centered_normalization_at_points {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) (hzero : u 0=0) (hdzero : fderiv ℝ u 0=0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ P : Finset (Space n),
      ∃ t : ℝ, 0 < t ∧ ∃ A : Space n ≃L[ℝ] Space n,
        BalancedNormalized ρ R (normalizedFunction u A t) ∧
        ∀ x ∈ P, A.symm x ∈ Metric.ball (0:Space n) (1/64:ℝ) := by
  obtain ⟨R,hR,H⟩ := centered_section_normalization_family hn hu hp hzero hdzero hρ hρ1 hbal
  refine ⟨R,hR,?_⟩
  intro P
  let t : ℝ := 1 + ∑ x ∈ P, |u ((64*R) • x)|
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨A,hin,hout⟩ := H t ht
  have hv0 : normalizedFunction u A t 0=0 := by simp [normalizedFunction,hzero]
  have hdz : fderiv ℝ (normalizedFunction u A t) 0=0 := by
    rw [fderiv_normalizedFunction hu]
    simp only [map_zero,hdzero,ContinuousLinearMap.zero_comp,smul_zero]
  refine ⟨t,ht,A,⟨contDiff_normalizedFunction hu A t,posDef_hessian_normalizedFunction hu hp A ht,
    affineMaximalOn_normalizedFunction hu hp hm A ht,hv0,hdz,
    sectionBalance_normalizedFunction hu hp hbal A ht,hin,hout⟩,?_⟩
  intro x hx
  have hxu : u ((64*R) • x) < t := by
    have HH := Finset.single_le_sum (fun point _ => abs_nonneg (u ((64*R) • point))) hx
    dsimp [t]
    linarith [le_abs_self (u ((64*R) • x))]
  have hsec : (64*R) • (A.symm x) ∈ tangentSection univ (normalizedFunction u A t) 0 1 := by
    refine ⟨mem_univ _,?_⟩
    rw [tangentHeight_normalizedFunction hu]
    simp only [map_zero,map_smul,ContinuousLinearEquiv.apply_symm_apply,tangentHeight,hzero,hdzero,
      sub_zero,zero_apply,smul_zero]
    rw [mul_comm,← div_eq_mul_inv]
    exact (div_lt_one ht).mpr hxu
  have hnorm := hout hsec
  rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
    abs_of_pos (show 0 < 64*R by linarith)] at hnorm
  rw [Metric.mem_ball,dist_zero_right]
  have hRp : 0 < R := by linarith
  nlinarith

end LinearizedNormalization


end
end AffineBernstein
end

end OAI
