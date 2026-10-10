import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.Alpha

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section

def Alpha (c x a b : ℝ) : ℝ := alpha x (c*psi x*a) (c*psi x*b)
def Beta (c x a b : ℝ) : ℝ := beta x (c*psi x*a) (c*psi x*b)
def scaleT (c x a b : ℝ) : ℝ := Real.sqrt (Alpha c x a b*Beta c x a b/psi x)
def scaleL (c x a b : ℝ) : ℝ := Alpha c x a b/scaleT c x a b
def scaleM (c x a b : ℝ) : ℝ := Beta c x a b/scaleT c x a b

lemma Alpha_eq {x : ℝ} (hx : |x| < 1) (c a b : ℝ) :
    Alpha c x a b = 1+c*psi₁ x*b := by
  rw [Alpha,alpha,psi₁_eq_base hx]
  ring

lemma Beta_eq {x : ℝ} (hx : |x| < 1) (c a b : ℝ) :
    Beta c x a b = 1-c*psi₁ x*a := by
  rw [Beta,beta,psi₁_eq_base hx]
  ring

lemma light_rescaling_pos {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    0 < Alpha c x a b ∧ 0 < Beta c x a b ∧ 0 < scaleT c x a b ∧
    0 < scaleL c x a b ∧ 0 < scaleM c x a b := by
  have hap := mul_pos (mul_pos hc (psi_pos hx)) ha
  have hbp := mul_pos (mul_pos hc (psi_pos hx)) hb
  obtain ⟨_,_,hA,hB⟩ := product_bounds hx hap hbp hal hbl
  have hT : 0 < scaleT c x a b := Real.sqrt_pos.mpr (div_pos (mul_pos hA hB) (psi_pos hx))
  exact ⟨hA,hB,hT,div_pos hA hT,div_pos hB hT⟩

lemma scaleT_sq {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    scaleT c x a b^2 = Alpha c x a b*Beta c x a b/psi x := by
  obtain ⟨hA,hB,_⟩ := light_rescaling_pos hc hx ha hb hal hbl
  exact Real.sq_sqrt (div_nonneg (mul_nonneg hA.le hB.le) (psi_pos hx).le)

lemma scaleL_mul_scaleM {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    scaleL c x a b*scaleM c x a b = psi x := by
  obtain ⟨hA,hB,_⟩ := light_rescaling_pos hc hx ha hb hal hbl
  rw [scaleL,scaleM,div_mul_div_comm,← pow_two,scaleT_sq hc hx ha hb hal hbl]
  field_simp [hA.ne',hB.ne']

lemma rescaled_product_bound {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    (scaleL c x a b*a)*(scaleM c x a b*b) ≤ c⁻¹^2 := by
  have hr := base_pos hx
  have hp := psi_pos hx
  have ha' := mul_pos (mul_pos hc hp) ha
  have hb' := mul_pos (mul_pos hc hp) hb
  have hp' : (c*psi x*a)*(c*psi x*b) ≤ (1+x)*(1-x) :=
    mul_le_mul hal.le hbl.le hb'.le (by linarith [abs_lt.mp hx])
  have hψ : 0 < psi x^2 := sq_pos_of_pos hp
  have hbound : c^2*(psi x*(a*b)) ≤ 1 := by
    have he : (c*psi x*a)*(c*psi x*b) = (c^2*(psi x*(a*b)))*psi x := by ring
    rw [he] at hp'
    have hg := psi_ge_base hx
    nlinarith
  have he : (scaleL c x a b*a)*(scaleM c x a b*b) = psi x*(a*b) := by
    rw [show (scaleL c x a b*a)*(scaleM c x a b*b) =
      (scaleL c x a b*scaleM c x a b)*(a*b) by ring,
      scaleL_mul_scaleM hc hx ha hb hal hbl]
  rw [he,inv_pow,inv_eq_one_div]
  exact (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by nlinarith)

lemma rescaled_square_bounds {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    (scaleL c x a b*a)^2 ≤ 3*c⁻¹^2 ∧ (scaleM c x a b*b)^2 ≤ 3*c⁻¹^2 := by
  obtain ⟨hA,hB,hT,_⟩ := light_rescaling_pos hc hx ha hb hal hbl
  have hp := psi_pos hx
  obtain ⟨hL,hM⟩ := light_squares hx (mul_pos (mul_pos hc hp) ha)
    (mul_pos (mul_pos hc hp) hb) hal hbl
  change Alpha c x a b*(c*psi x*a)^2 ≤ 3*Beta c x a b*psi x at hL
  change Beta c x a b*(c*psi x*b)^2 ≤ 3*Alpha c x a b*psi x at hM
  have heL : c^2*(scaleL c x a b*a)^2 =
      Alpha c x a b*(c*psi x*a)^2/(Beta c x a b*psi x) := by
    rw [scaleL,mul_pow,div_pow,scaleT_sq hc hx ha hb hal hbl]
    field_simp [hA.ne',hB.ne',hp.ne']
  have heM : c^2*(scaleM c x a b*b)^2 =
      Beta c x a b*(c*psi x*b)^2/(Alpha c x a b*psi x) := by
    rw [scaleM,mul_pow,div_pow,scaleT_sq hc hx ha hb hal hbl]
    field_simp [hA.ne',hB.ne',hp.ne']
  have hL' : c^2*(scaleL c x a b*a)^2 ≤ 3 := by
    rw [heL]
    exact (div_le_iff₀ (mul_pos hB hp)).mpr (by nlinarith)
  have hM' : c^2*(scaleM c x a b*b)^2 ≤ 3 := by
    rw [heM]
    exact (div_le_iff₀ (mul_pos hA hp)).mpr (by nlinarith)
  rw [inv_pow,← div_eq_mul_inv]
  exact ⟨(le_div_iff₀ (sq_pos_of_pos hc)).mpr (by nlinarith),
    (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by nlinarith)⟩

lemma rescaled_kappa_bounds {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    (1/3 : ℝ) ≤ kappa x/(Alpha c x a b*Beta c x a b) ∧
    (1/3 : ℝ) ≤ kappa x/scaleT c x a b^2 ∧
    (scaleT c x a b^2)⁻¹ ≤ (3/2 : ℝ) := by
  have hp := psi_pos hx
  obtain ⟨hA,hB,_⟩ := light_rescaling_pos hc hx ha hb hal hbl
  obtain ⟨h₁,h₂,h₃⟩ := kappa_product_bounds hx (mul_pos (mul_pos hc hp) ha)
    (mul_pos (mul_pos hc hp) hb) hal hbl
  change (1/3 : ℝ) ≤ kappa x/(Alpha c x a b*Beta c x a b) at h₁
  change (1/3 : ℝ) ≤ psi x*kappa x/(Alpha c x a b*Beta c x a b) at h₂
  change psi x/(Alpha c x a b*Beta c x a b) ≤ (3/2 : ℝ) at h₃
  refine ⟨h₁,?_,?_⟩
  · rw [scaleT_sq hc hx ha hb hal hbl]
    convert h₂ using 1
    field_simp
  · rw [scaleT_sq hc hx ha hb hal hbl,inv_div]
    exact h₃

lemma rescaled_sum_identity {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    scaleT c x a b*(scaleL c x a b*a+scaleM c x a b*b) = a+b := by
  have hT := (light_rescaling_pos hc hx ha hb hal hbl).2.2.1
  rw [scaleL,scaleM]
  field_simp
  rw [Alpha_eq hx,Beta_eq hx]
  ring

lemma rescaled_drift_bounds {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    scaleT c x a b*(scaleL c x a b*a+scaleM c x a b*b) ≤ 2/(c*psi x) ∧
    (scaleL c x a b*a+scaleM c x a b*b)/scaleT c x a b ≤ 3/c := by
  have hp := psi_pos hx
  have hs : c*psi x*(a+b) ≤ 2 := by nlinarith
  obtain ⟨hA,hB,hT,_⟩ := light_rescaling_pos hc hx ha hb hal hbl
  have hlo := (product_bounds hx (mul_pos (mul_pos hc hp) ha)
    (mul_pos (mul_pos hc hp) hb) hal hbl).1
  change (2/3 : ℝ) ≤ Alpha c x a b*Beta c x a b at hlo
  refine ⟨?_,?_⟩
  · rw [rescaled_sum_identity hc hx ha hb hal hbl]
    exact (le_div_iff₀ (mul_pos hc hp)).mpr (by nlinarith)
  · have he : (scaleL c x a b*a+scaleM c x a b*b)/scaleT c x a b =
        psi x*(a+b)/(Alpha c x a b*Beta c x a b) := by
      have hh := rescaled_sum_identity hc hx ha hb hal hbl
      have hh' : scaleL c x a b*a+scaleM c x a b*b = (a+b)/scaleT c x a b :=
        (eq_div_iff hT.ne').mpr (by nlinarith)
      rw [hh',div_div,← pow_two,scaleT_sq hc hx ha hb hal hbl]
      field_simp
    rw [he]
    apply (div_le_div_iff₀ (mul_pos hA hB) hc).mpr
    nlinarith

end
end CurrentKS.Scalar

end OAI
