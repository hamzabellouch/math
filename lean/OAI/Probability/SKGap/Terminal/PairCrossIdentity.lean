import Mathlib
import OAI.Probability.SKGap.Terminal.SpinLocalField
import OAI.Probability.SKGap.Terminal.PairRationalBounds

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

def pairDensity (a b u : ℝ) (x y : Bool) : ℝ :=
  (1+u*spinValue x*spinValue y)/(1+u*a*b)
def pairInterMean (a b u : ℝ) (F : Bool→Bool→ℝ) : ℝ :=
  pairMean a b (fun x y=>pairDensity a b u x y*F x y)
def pairResidual (a u : ℝ) (x y : Bool) : ℝ :=
  (spinValue x-a)*(1-u*spinValue x*spinValue y)/(1+u*a*spinValue y)
def pairVariance (a u : ℝ) (y : Bool) : ℝ :=
  (1-a^2)*(1-u^2)/(1+u*a*spinValue y)^2

def pairGrad₁ (b p r : ℝ) (y : Bool) : ℝ := p+r*(spinValue y-b)
def pairGrad₂ (a s r : ℝ) (x : Bool) : ℝ := s+r*(spinValue x-a)

lemma pairSign_abs (x : Bool) : |spinValue x|=1 := by cases x <;> norm_num [spinValue]
lemma pairSign_sq (x : Bool) : spinValue x^2=1 := by cases x <;> norm_num [spinValue]

lemma pairDenominator_pos {u a b : ℝ} (hu : |u| ≤ 1/4) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    0 < 1+u*a*b := by
  have hh := (pair_factor_control hu (abs_mul_le_one_pair ha hb)).1
  rw [← mul_assoc] at hh
  linarith only [hh]

lemma reciprocal_affine (c d v : ℝ) (y : Bool) (hv : |v| < 1) :
    (c+d*spinValue y)/(1+v*spinValue y)=
      (c-v*d)/(1-v^2)+spinValue y*((d-v*c)/(1-v^2)) := by
  have hv' := abs_lt.mp hv
  have h₁ : 1+v ≠ 0 := by linarith only [hv'.1]
  have h₂ : 1-v ≠ 0 := by linarith only [hv'.2]
  have h₃ : 1-v^2 ≠ 0 := by
    have he : 1-v^2=(1+v)*(1-v) := by ring
    rw [he];exact mul_ne_zero h₁ h₂
  cases y <;> simp only [spinValue,Bool.false_eq_true,ite_false,ite_true,mul_one,mul_neg_one,← sub_eq_add_neg]
  · field_simp [h₂,h₃]
    ring
  · field_simp [h₁,h₃]
    ring

lemma pair_gradient_reciprocal {a b u p r : ℝ} (ha : |a| ≤ 1) (hu : |u| ≤ 1/4) (y : Bool) :
    pairGrad₁ b p r y/(1+u*a*spinValue y)=
      (p-(b+u*a)*r)/(1-u^2*a^2)+
      spinValue y*((r*(1+u*a*b)-u*a*p)/(1-u^2*a^2)) := by
  have hv : |u*a| < 1 := by
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_left ha (abs_nonneg u)
    nlinarith only [hu,hh]
  have he := reciprocal_affine (p-r*b) r (u*a) y hv
  have hg : pairGrad₁ b p r y =p-r*b+r*spinValue y := by unfold pairGrad₁;ring
  rw [hg,he]
  congr 1
  · congr 1 <;> ring
  · congr 1
    congr 1 <;> ring

lemma pair_cross_coefficient_identity {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    (1-u^2)/(1+u*a*b)*
      (((r*(1+u*a*b)-u*a*p)/(1-u^2*a^2))*
        ((r*(1+u*a*b)-u*b*s)/(1-u^2*b^2))-
        u*((p-(b+u*a)*r)/(1-u^2*a^2))*((s-(a+u*b)*r)/(1-u^2*b^2)))=
      pairCrossPolynomial a b u p s r := by
  have hd₀ := (pairDenominator_pos hu ha hb).ne'
  have hd₁ : 1-u^2*a^2 ≠ 0 := by
    have h₁ := pairDenominator_pos hu ha (by norm_num : |(1:ℝ)| ≤ 1)
    have h₂ := pairDenominator_pos hu ha (by norm_num : |(-1:ℝ)| ≤ 1)
    have he : 1-u^2*a^2=(1+u*a*1)*(1+u*a*(-1)) := by ring
    rw [he];exact mul_ne_zero h₁.ne' h₂.ne'
  have hd₂ : 1-u^2*b^2 ≠ 0 := by
    have h₁ := pairDenominator_pos hu hb (by norm_num : |(1:ℝ)| ≤ 1)
    have h₂ := pairDenominator_pos hu hb (by norm_num : |(-1:ℝ)| ≤ 1)
    have he : 1-u^2*b^2=(1+u*b*1)*(1+u*b*(-1)) := by ring
    rw [he];exact mul_ne_zero h₁.ne' h₂.ne'
  unfold pairCrossPolynomial pairK pairR
  field_simp [hd₀,hd₁,hd₂]
  ring

lemma pair_cross_pointwise (a b u p s r : ℝ) (x y : Bool) :
    pairDensity a b u x y*(pairResidual a u x y*pairGrad₁ b p r y*
      (pairResidual b u y x*pairGrad₂ a s r x))=
    ((1-u^2)/(1+u*a*b))*((spinValue x-a)*(spinValue y-b)*
      (1-u*spinValue x*spinValue y)*(pairGrad₁ b p r y/(1+u*a*spinValue y))*
      (pairGrad₂ a s r x/(1+u*b*spinValue x))) := by
  unfold pairDensity pairResidual
  have he : (1+u*spinValue x*spinValue y)*(1-u*spinValue x*spinValue y)*
      (1-u*spinValue y*spinValue x)=(1-u^2)*(1-u*spinValue x*spinValue y) := by
    cases x <;> cases y <;> simp only [spinValue,Bool.false_eq_true,ite_false,ite_true] <;> ring
  calc
    _ = ((1+u*spinValue x*spinValue y)*(1-u*spinValue x*spinValue y)*(1-u*spinValue y*spinValue x))*
      ((spinValue x-a)*(spinValue y-b)*pairGrad₁ b p r y*pairGrad₂ a s r x)/
      ((1+u*a*b)*(1+u*a*spinValue y)*(1+u*b*spinValue x)) := by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
    _ = _ := by
      rw [he]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

lemma pair_cross_exact {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    pairInterMean a b u (fun x y=>pairResidual a u x y*pairGrad₁ b p r y*
      (pairResidual b u y x*pairGrad₂ a s r x))=
      (1-a^2)*(1-b^2)*pairCrossPolynomial a b u p s r := by
  unfold pairInterMean
  simp_rw [pair_cross_pointwise]
  rw [pairMean_mul]
  have hh (x y : Bool) :
      (spinValue x-a)*(spinValue y-b)*(1-u*spinValue x*spinValue y)*
        (pairGrad₁ b p r y/(1+u*a*spinValue y))*
        (pairGrad₂ a s r x/(1+u*b*spinValue x))=
      (spinValue x-a)*(spinValue y-b)*(1-u*spinValue x*spinValue y)*
        ((p-(b+u*a)*r)/(1-u^2*a^2)+spinValue y*((r*(1+u*a*b)-u*a*p)/(1-u^2*a^2)))*
        ((s-(a+u*b)*r)/(1-u^2*b^2)+spinValue x*((r*(1+u*b*a)-u*b*s)/(1-u^2*b^2))) := by
    rw [pair_gradient_reciprocal ha hu]
    change _ * (pairGrad₁ a s r x / _) = _
    rw [pair_gradient_reciprocal hb hu]
  simp_rw [hh]
  rw [pair_polynomial_cross_mean]
  have he : 1+u*b*a=1+u*a*b := by ring
  rw [he]
  calc
    _ = (1-a^2)*(1-b^2)*((1-u^2)/(1+u*a*b)*
      (((r*(1+u*a*b)-u*a*p)/(1-u^2*a^2))*
        ((r*(1+u*a*b)-u*b*s)/(1-u^2*b^2))-
        u*((p-(b+u*a)*r)/(1-u^2*a^2))*((s-(a+u*b)*r)/(1-u^2*b^2)))) := by ring
    _ = _ := by rw [pair_cross_coefficient_identity ha hb hu]
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real

lemma pair_variance_nonneg {a u : ℝ} (ha : |a| ≤ 1) (hu : |u| ≤ 1/4) (y : Bool) :
    0 ≤ pairVariance a u y := by
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hh := (pair_square_factor_control hu).1
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr ha2) (by linarith only [hh])) (sq_nonneg _)

lemma pair_density_nonneg {a b u : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hu : |u| ≤ 1/4) (x y : Bool) : 0 ≤ pairDensity a b u x y := by
  exact div_nonneg (pairDenominator_pos hu (pairSign_abs x).le (pairSign_abs y).le).le
    (pairDenominator_pos hu ha hb).le

lemma pair_variance_product (a b u : ℝ) (x y : Bool) :
    pairDensity a b u x y*(pairVariance a u y*pairVariance b u x)=
      (1-a^2)*(1-b^2)*pairRationalWeight a b u (spinValue x) (spinValue y) := by
  unfold pairDensity pairVariance pairRationalWeight
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma pair_weighted_product (a b u p s r : ℝ) :
    pairInterMean a b u (fun x y=>pairVariance a u y*pairGrad₁ b p r y*
      (pairVariance b u x*pairGrad₂ a s r x))=
    (1-a^2)*(1-b^2)*pairMean a b (fun x y=>pairRationalWeight a b u (spinValue x) (spinValue y)*
      (pairGrad₁ b p r y*pairGrad₂ a s r x)) := by
  unfold pairInterMean
  rw [← pairMean_mul]
  congr 1
  funext x y
  calc
    _ = (pairDensity a b u x y*(pairVariance a u y*pairVariance b u x))*
      (pairGrad₁ b p r y*pairGrad₂ a s r x) := by ring
    _ = _ := by rw [pair_variance_product];ring

lemma pair_abs_weighted_product {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    pairInterMean a b u (fun x y=>|pairVariance a u y*pairGrad₁ b p r y*
      (pairVariance b u x*pairGrad₂ a s r x)|)=
    (1-a^2)*(1-b^2)*pairMean a b (fun x y=>pairRationalWeight a b u (spinValue x) (spinValue y)*
      |pairGrad₁ b p r y*pairGrad₂ a s r x|) := by
  unfold pairInterMean
  rw [← pairMean_mul]
  congr 1
  funext x y
  have h₁ := pair_variance_nonneg ha hu y
  have h₂ := pair_variance_nonneg hb hu x
  simp only [abs_mul,abs_of_nonneg h₁,abs_of_nonneg h₂]
  calc
    _ = (pairDensity a b u x y*(pairVariance a u y*pairVariance b u x))*
      (|pairGrad₁ b p r y| * |pairGrad₂ a s r x|) := by ring
    _ = _ := by rw [pair_variance_product];ring

lemma pair_weighted_error {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    |pairMean a b (fun x y=>pairRationalWeight a b u (spinValue x) (spinValue y)*
      (pairGrad₁ b p r y*pairGrad₂ a s r x))-p*s| ≤
    1216*|u| * pairMean a b (fun x y=>|pairGrad₁ b p r y*pairGrad₂ a s r x|) := by
  have he : p*s=pairMean a b (fun x y=>pairGrad₁ b p r y*pairGrad₂ a s r x) :=
    (pair_gradient_mean a b p s r).symm
  rw [he,← pairMean_sub]
  apply (abs_pairMean_le ha hb _).trans
  rw [← pairMean_mul]
  apply pairMean_mono ha hb
  intro x y
  have hh := (pairRationalWeight_bounds ha hb hu (pairSign_abs x).le (pairSign_abs y).le).2.2
  have ht : pairRationalWeight a b u (spinValue x) (spinValue y)*
      (pairGrad₁ b p r y*pairGrad₂ a s r x)-(pairGrad₁ b p r y*pairGrad₂ a s r x)=
      (pairRationalWeight a b u (spinValue x) (spinValue y)-1)*
      (pairGrad₁ b p r y*pairGrad₂ a s r x) := by ring
  rw [ht,abs_mul]
  exact mul_le_mul_of_nonneg_right hh (abs_nonneg _)

lemma pair_abs_cost_lower {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    (1-a^2)*(1-b^2)*pairMean a b (fun x y=>|pairGrad₁ b p r y*pairGrad₂ a s r x|)/256 ≤
    pairInterMean a b u (fun x y=>|pairVariance a u y*pairGrad₁ b p r y*
      (pairVariance b u x*pairGrad₂ a s r x)|) := by
  rw [pair_abs_weighted_product ha hb hu]
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hb2 : b^2 ≤ 1 := by nlinarith only [sq_abs b,abs_nonneg b,hb]
  have hAB : 0 ≤ (1-a^2)*(1-b^2) := mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2)
  have he : (1-a^2)*(1-b^2)*pairMean a b (fun x y=>|pairGrad₁ b p r y*pairGrad₂ a s r x|)/256=
      (1-a^2)*(1-b^2)*((1/256)*pairMean a b (fun x y=>|pairGrad₁ b p r y*pairGrad₂ a s r x|)) := by ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hAB
  rw [← pairMean_mul]
  apply pairMean_mono ha hb
  intro x y
  exact mul_le_mul_of_nonneg_right
    (pairRationalWeight_bounds ha hb hu (pairSign_abs x).le (pairSign_abs y).le).1 (abs_nonneg _)

lemma pair_density_variance_lower {a b u : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) (x y : Bool) :
    (1-a^2)/32 ≤ pairDensity a b u x y*pairVariance a u y := by
  have hn : 1/2 ≤ 1+u*spinValue x*spinValue y := by
    simpa only [mul_assoc] using (pair_factor_control hu (abs_mul_le_one_pair (pairSign_abs x).le (pairSign_abs y).le)).1
  have hs := (pair_square_factor_control hu).1
  have hd₀ := pair_factor_control hu (abs_mul_le_one_pair ha hb)
  have hd₁ := pair_factor_control hu (abs_mul_le_one_pair ha (pairSign_abs y).le)
  have hd02 : 1+u*a*b ≤ 2 := by simpa only [mul_assoc] using hd₀.2.1
  have hd12 : 1+u*a*spinValue y ≤ 2 := by simpa only [mul_assoc] using hd₁.2.1
  have hd10 : 0 ≤ 1+u*a*spinValue y := (pairDenominator_pos hu ha (pairSign_abs y).le).le
  have hd00 := pairDenominator_pos hu ha hb
  have hdd : 0 < (1+u*a*b)*(1+u*a*spinValue y)^2 := mul_pos hd00 (sq_pos_of_pos (pairDenominator_pos hu ha (pairSign_abs y).le))
  have hd : (1+u*a*b)*(1+u*a*spinValue y)^2 ≤ 8 := by
    have hh : (1+u*a*spinValue y)^2 ≤ 4 := by nlinarith only [hd12,hd10]
    nlinarith only [mul_le_mul hd02 hh (sq_nonneg (1+u*a*spinValue y)) (by norm_num : (0:ℝ) ≤ 2)]
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hA := sub_nonneg.mpr ha2
  have hn' : 1/4 ≤ (1+u*spinValue x*spinValue y)*(1-u^2) := by
    nlinarith only [mul_le_mul hn hs (by norm_num : (0:ℝ) ≤ 1/2) (by linarith only [hn] : 0 ≤ 1+u*spinValue x*spinValue y)]
  have he : pairDensity a b u x y*pairVariance a u y=
      ((1-a^2)*((1+u*spinValue x*spinValue y)*(1-u^2)))/
      ((1+u*a*b)*(1+u*a*spinValue y)^2) := by
    unfold pairDensity pairVariance
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]
  apply (le_div_iff₀ hdd).mpr
  have h₁ := mul_le_mul_of_nonneg_left hd (div_nonneg hA (by norm_num : (0:ℝ) ≤ 32))
  have h₂ := mul_le_mul_of_nonneg_left hn' hA
  nlinarith only [h₁,h₂]
end SKGap

end
end

end OAI
