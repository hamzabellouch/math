import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ScalarPsi

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open scoped ContDiff

def kappa₁ (x : ℝ) : ℝ :=
  4*x/(9*psi x^5)+20*x*(3+x^2)/(27*psi x^8)

lemma hasDerivAt_kappa {x : ℝ} (hx : |x| < 1) : HasDerivAt kappa (kappa₁ x) x := by
  have hp := hasDerivAt_psi hx
  have hw : psi x ≠ 0 := (psi_pos hx).ne'
  have hd := (((hasDerivAt_const x (3:ℝ)).add ((hasDerivAt_id x).pow 2)).const_mul 2).div
    ((hp.pow 5).const_mul 9) (by positivity : (9:ℝ)*psi x^5 ≠ 0)
  convert hd using 1 <;> try rfl
  simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,zero_add,Pi.add_apply]
  unfold kappa₁ psi₁
  field_simp
  ring

lemma strip_interior {σ x : ℝ} (hσ : 0 < σ) (hx : |x| ≤ 1-σ/2) : |x| < 1 := by linarith

lemma strip_base {σ x : ℝ} (hσ : 0 < σ) (hx : |x| ≤ 1-σ/2) : σ/2 ≤ 1-x^2 := by
  have hi := strip_interior hσ hx
  have ha := abs_nonneg x
  have h1 : |x| ≤ 1 := hi.le
  have hh := mul_nonneg (sub_nonneg.mpr h1) ha
  rw [sub_mul,one_mul] at hh
  nlinarith [sq_abs x]

lemma strip_denominator {σ x : ℝ} (hσ : 0 < σ) (hx : |x| ≤ 1-σ/2)
    (k : ℕ) (hk : k ≤ 9) : σ^3/8 ≤ psi x^k := by
  have hi := strip_interior hσ hx
  have hp := psi_pos hi
  have h1 := psi_le_one hi
  have hb := strip_base hσ hx
  have hc : (σ/2)^3 ≤ (1-x^2)^3 := pow_le_pow_left₀ (by positivity) hb 3
  have he : (1-x^2)^3 = psi x^9 := by rw [← psi_cube hi,← pow_mul]
  have hpow : psi x^9 ≤ psi x^k := by exact pow_le_pow_of_le_one hp.le h1 hk
  calc
    σ^3/8 = (σ/2)^3 := by ring
    _ ≤ _ := hc.trans_eq he
    _ ≤ _ := hpow

lemma scalar_fraction_strip {σ x u : ℝ} (hσ : 0 < σ) (hx : |x| ≤ 1-σ/2)
    (k : ℕ) (hk : k ≤ 9) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hu : |u| ≤ b) :
    |u/(a*psi x^k)| ≤ (8*b/a)/σ^3 := by
  have hp := psi_pos (strip_interior hσ hx)
  have hd := strip_denominator hσ hx k hk
  have ha' : 0 < a*psi x^k := mul_pos ha (pow_pos hp _)
  rw [abs_div,abs_of_pos ha']
  apply (div_le_div_iff₀ ha' (pow_pos hσ _)).mpr
  have hh := mul_le_mul_of_nonneg_left hd hb
  have hu' := mul_le_mul_of_nonneg_right hu (pow_nonneg hσ.le 3)
  have he : (8*b/a)*(a*psi x^k) = 8*b*psi x^k := by field_simp
  rw [he]
  nlinarith only [hh,hu']

theorem strip_derivative_bounds {σ x : ℝ} (hσ : 0 < σ) (hx : |x| ≤ 1-σ/2) :
    |psi₁ x| ≤ 800/σ^3 ∧ |kappa x| ≤ 800/σ^3 ∧ |kappa₁ x| ≤ 800/σ^3 := by
  have hi := strip_interior hσ hx
  have hx1 : |x| ≤ 1 := hi.le
  have hx2 : x^2 ≤ 1 := by nlinarith [sq_abs x,abs_nonneg x]
  have hn1 : |(-2:ℝ)*x| ≤ 2 := by rw [abs_mul]; norm_num; linarith
  have hn2 : |2*(3+x^2)| ≤ 8 := by rw [abs_of_nonneg (by positivity)]; nlinarith
  have hn3 : |(4:ℝ)*x| ≤ 4 := by rw [abs_mul]; norm_num; linarith
  have hn4 : |20*x*(3+x^2)| ≤ 80 := by
    rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤20),abs_of_nonneg (by positivity : (0:ℝ)≤3+x^2)]
    nlinarith [abs_nonneg x]
  have h₁ := scalar_fraction_strip hσ hx 2 (by norm_num) (by norm_num : (0:ℝ)<3) (by norm_num : (0:ℝ)≤2) hn1
  have h₂ := scalar_fraction_strip hσ hx 5 (by norm_num) (by norm_num : (0:ℝ)<9) (by norm_num : (0:ℝ)≤8) hn2
  have h₃ := scalar_fraction_strip hσ hx 5 (by norm_num) (by norm_num : (0:ℝ)<9) (by norm_num : (0:ℝ)≤4) hn3
  have h₄ := scalar_fraction_strip hσ hx 8 (by norm_num) (by norm_num : (0:ℝ)<27) (by norm_num : (0:ℝ)≤80) hn4
  refine ⟨h₁.trans ?_,h₂.trans ?_,?_⟩
  · exact div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hσ.le 3)
  · exact div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hσ.le 3)
  · calc
      |kappa₁ x| ≤ |4*x/(9*psi x^5)|+|20*x*(3+x^2)/(27*psi x^8)| := abs_add_le _ _
      _ ≤ (8*4/9)/σ^3+(8*80/27)/σ^3 := add_le_add h₃ h₄
      _ ≤ 800/σ^3 := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hσ.le 3)

end
end CurrentKS.Scalar

end OAI
