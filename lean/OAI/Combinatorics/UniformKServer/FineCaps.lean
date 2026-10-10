import Mathlib

namespace OAI

                               
section

/-! Companion §03, fine cap algebra.  The tolerance hypotheses below are the
actual absolute choices in Lemma caps; there is no assumed cap feasibility. -/
namespace UniformKServer.FineCaps
noncomputable section
open Finset

/-- Convex interpolation preserves the same multiplicative endpoint error. -/
theorem interpolate {a b A B c ξ : ℝ} (hc : c ∈ Set.Icc (0:ℝ) 1)
    (ha : (1+ξ)⁻¹*a ≤ A ∧ A ≤ (1+ξ)*a)
    (hb : (1+ξ)⁻¹*b ≤ B ∧ B ≤ (1+ξ)*b) :
    (1+ξ)⁻¹*((1-c)*a+c*b) ≤ (1-c)*A+c*B ∧
      (1-c)*A+c*B ≤ (1+ξ)*((1-c)*a+c*b) := by
  have h0 : 0 ≤ 1-c := by linarith [hc.2]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left ha.1 h0,
      mul_le_mul_of_nonneg_left hb.1 hc.1]
  · nlinarith [mul_le_mul_of_nonneg_left ha.2 h0,
      mul_le_mul_of_nonneg_left hb.2 hc.1]

theorem regular_factor {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hy' : y ≤ x/4) :
    1-2*x ≤ (1-x)*(1-y) ∧ (1-x)*(1+y) ≤ 1 := by
  constructor <;> nlinarith [mul_nonneg hx hy]

theorem dominant_factor {x y : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/4)
    (hy : 0 ≤ y) (hy' : y ≤ x/4) :
    1 ≤ (1+x)*(1-y) ∧ (1+x)*(1+y) ≤ 1+2*x := by
  have hprod : x*y ≤ y/4 := by nlinarith [mul_le_mul_of_nonneg_right hx' hy]
  constructor <;> nlinarith

/-- Both explicit factors at once, including zero true flexible mass. -/
theorem caps {ell lam e T F γ ε f : ℝ} (hell : 1 ≤ ell)
    (hlam : 0 ≤ lam) (hlam' : lam ≤ 1/4) (he : 0 ≤ e) (he' : e ≤ lam/4)
    (hγ : 4*lam ≤ γ) (hε : 4*lam ≤ ε) (hT : 0 ≤ T)
    (hF : |F-T| ≤ (e/ell)*T) (hf : f ≤ (1-γ/ell)*T) :
    (f ≤ (1-lam/ell)*F ∧ (1-lam/ell)*F ≤ T) ∧
      (T ≤ (1+lam/ell)*F ∧ (1+lam/ell)*F ≤ (1+ε/ell)*T) := by
  have hell0 : 0 < ell := by linarith
  have hx : 0 ≤ lam/ell := div_nonneg hlam hell0.le
  have hx' : lam/ell ≤ 1/4 := by
    apply (div_le_iff₀ hell0).2
    nlinarith
  have hy : 0 ≤ e/ell := div_nonneg he hell0.le
  have hy' : e/ell ≤ (lam/ell)/4 := by
    apply (div_le_iff₀ hell0).2
    rw [div_mul_eq_mul_div,div_mul_cancel₀ _ (ne_of_gt hell0)]
    exact he'
  have hFlo : (1-e/ell)*T ≤ F := by linarith [(abs_le.mp hF).1]
  have hFhi : F ≤ (1+e/ell)*T := by linarith [(abs_le.mp hF).2]
  have hra := regular_factor hx hy hy'
  have hda := dominant_factor hx hx' hy hy'
  have hγ' : 2*(lam/ell) ≤ γ/ell := by
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hell0.le
  have hε' : 2*(lam/ell) ≤ ε/ell := by
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hell0.le
  have hrlo := mul_le_mul_of_nonneg_left hFlo (by linarith : 0 ≤ 1-lam/ell)
  have hrhi := mul_le_mul_of_nonneg_left hFhi (by linarith : 0 ≤ 1-lam/ell)
  have hdlo := mul_le_mul_of_nonneg_left hFlo (by linarith : 0 ≤ 1+lam/ell)
  have hdhi := mul_le_mul_of_nonneg_left hFhi (by linarith : 0 ≤ 1+lam/ell)
  have hrT := mul_le_mul_of_nonneg_right hra.1 hT
  have hrT' := mul_le_mul_of_nonneg_right hra.2 hT
  have hdT := mul_le_mul_of_nonneg_right hda.1 hT
  have hdT' := mul_le_mul_of_nonneg_right hda.2 hT
  have hγT := mul_le_mul_of_nonneg_right hγ' hT
  have hεT := mul_le_mul_of_nonneg_right hε' hT
  constructor <;> constructor <;> nlinarith only [hf,hrlo,hrhi,hdlo,hdhi,hrT,hrT',hdT,hdT',hγT,hεT]

/-- A held convex interpolation costs no more variation than the two
persistent endpoint trackers. -/
theorem interpolation_variation {a b A B c : ℝ} (hc : c ∈ Set.Icc (0:ℝ) 1) :
    |((1-c)*A+c*B)-((1-c)*a+c*b)| ≤ |A-a|+|B-b| := by
  have h0 : 0 ≤ 1-c := by linarith [hc.2]
  calc
    _ = |(1-c)*(A-a)+c*(B-b)| := by congr 1; ring
    _ ≤ |(1-c)*(A-a)|+|c*(B-b)| := abs_add_le _ _
    _ = (1-c)*|A-a|+c*|B-b| := by rw [abs_mul,abs_mul,abs_of_nonneg h0,abs_of_nonneg hc.1]
    _ ≤ _ := add_le_add
      (mul_le_of_le_one_left (abs_nonneg _) (by linarith [hc.1]))
      (mul_le_of_le_one_left (abs_nonneg _) hc.2)

/-- Changing membership in the noncore set costs one bounded endpoint value;
no fresh tracker is initialized. -/
theorem selected_variation (a b : Bool) {x y M : ℝ} (hx : |x| ≤ M)
    (hy : |y| ≤ M) :
    |(if b then y else 0)-(if a then x else 0)| ≤
      |y-x|+(if a=b then 0 else M) := by
  cases a <;> cases b <;> simp only [Bool.false_eq_true,Bool.true_eq_false,
    ↓reduceIte,sub_zero,zero_sub,abs_neg,abs_zero,add_zero]
  · exact abs_nonneg _
  · linarith [abs_nonneg (y-x)]
  · linarith [abs_nonneg (y-x)]
  · exact le_rfl

end
end UniformKServer.FineCaps

end

end OAI
