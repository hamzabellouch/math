import Mathlib
import OAI.Probability.SKGap.Terminal.PairCrossIdentity

namespace OAI

section
noncomputable section
namespace SKGap
open Real

lemma abs_pair_ps_coefficient {a b u : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    |pairK a b u*(-u+u^2*a*b)+u| ≤ 66*u^2 := by
  have hk := pairK_bounds ha hb hu
  have hk0 : 0 ≤ pairK a b u := by linarith only [hk.2.1]
  have he : pairK a b u*(-u+u^2*a*b)+u=
      -(pairK a b u-1)*u+pairK a b u*u^2*(a*b) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_neg,abs_mul,abs_mul,abs_of_nonneg hk0,abs_of_nonneg (sq_nonneg u)]
  have h₁ := mul_le_mul_of_nonneg_right hk.1 (abs_nonneg u)
  have h₂ := mul_le_mul (mul_le_mul_of_nonneg_right hk.2.2 (sq_nonneg u))
    (abs_mul_le_one_pair ha hb) (abs_nonneg (a*b)) (by positivity : (0:ℝ) ≤ 2*u^2)
  nlinarith only [h₁,h₂,sq_abs u]

lemma abs_pair_mixed_coefficient {a b u : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    |pairK a b u*u^2*b*(1-a^2)| ≤ 2*u^2 ∧
    |pairK a b u*u^2*a*(1-b^2)| ≤ 2*u^2 := by
  have hk := pairK_bounds ha hb hu
  have hk0 : 0 ≤ pairK a b u := by linarith only [hk.2.1]
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hb2 : b^2 ≤ 1 := by nlinarith only [sq_abs b,abs_nonneg b,hb]
  have hA : |1-a^2| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr ha2)];linarith [sq_nonneg a]
  have hB : |1-b^2| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hb2)];linarith [sq_nonneg b]
  have hh (x y : ℝ) (hxy : |x*y| ≤ 1) : |pairK a b u*u^2*x*y| ≤ 2*u^2 := by
    rw [mul_assoc (pairK a b u*u^2),abs_mul,abs_mul,abs_of_nonneg hk0,abs_of_nonneg (sq_nonneg u)]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right hk.2.2 (sq_nonneg u)) hxy
      (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  exact ⟨hh b (1-a^2) (abs_mul_le_one_pair hb hA),hh a (1-b^2) (abs_mul_le_one_pair ha hB)⟩

lemma mul_lower_from_abs {c x B : ℝ} (hc : |c| ≤ B) : -B*|x| ≤ c*x := by
  have hh := neg_abs_le (c*x)
  rw [abs_mul] at hh
  have hm := mul_le_mul_of_nonneg_right hc (abs_nonneg x)
  linarith only [hh,hm]

lemma pairCrossPolynomial_lower {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    r^2/2-66*u^2*|p*s|-2*u^2*|r*p|-2*u^2*|r*s| ≤
      pairCrossPolynomial a b u p s r+u*(p*s) := by
  have hps := mul_lower_from_abs (x:=p*s) (abs_pair_ps_coefficient ha hb hu)
  have hrp := mul_lower_from_abs (x:=r*p) (abs_pair_mixed_coefficient ha hb hu).1
  have hrs := mul_lower_from_abs (x:=r*s) (abs_pair_mixed_coefficient ha hb hu).2
  have hr := mul_le_mul_of_nonneg_right (pairKR_lower ha hb hu) (sq_nonneg r)
  unfold pairCrossPolynomial
  nlinarith only [hps,hrp,hrs,hr]

lemma pair_young_cost (u r p : ℝ) :
    2*u^2*|r*p| ≤ r^2/4+4*u^4*p^2 := by
  rw [abs_mul]
  have he : (|r|/2-2*u^2*|p|)^2=r^2/4-2*u^2*|r| * |p|+4*u^4*p^2 := by
    ring_nf
    rw [sq_abs r,sq_abs p]
    ring
  nlinarith only [sq_nonneg (|r|/2-2*u^2*|p|),he]

lemma pair_signed_cross_lower {a b u p s r z q : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000)
    (hq : |p*s| ≤ q) (hz : |z-p*s| ≤ 1216*|u| * q) :
    -1282*u^2*q-4*u^4*(p^2+s^2) ≤ pairCrossPolynomial a b u p s r+u*z := by
  have h₁ := pairCrossPolynomial_lower (p:=p) (s:=s) (r:=r) ha hb hu
  have h₂ := pair_young_cost u r p
  have h₃ := pair_young_cost u r s
  have h₄ := mul_le_mul_of_nonneg_left hq (show 0 ≤ 66*u^2 by positivity)
  have hz' : -1216*u^2*q ≤ u*(z-p*s) := by
    have hh := neg_abs_le (u*(z-p*s))
    rw [abs_mul] at hh
    have hm := mul_le_mul_of_nonneg_left hz (abs_nonneg u)
    have he : |u| * (1216*|u| * q)=1216*u^2*q := by
      ring_nf
      rw [sq_abs u]
      ring
    rw [he] at hm
    linarith only [hh,hm]
  nlinarith only [h₁,h₂,h₃,h₄,hz']
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real

lemma pair_energy_lower {a b u p r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    (1-a^2)*(1-b^2)*p^2/32 ≤
      pairInterMean a b u (fun _x y=>pairVariance a u y*(pairGrad₁ b p r y)^2) := by
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hb2 : b^2 ≤ 1 := by nlinarith only [sq_abs b,abs_nonneg b,hb]
  have hA := sub_nonneg.mpr ha2
  have hB := sub_nonneg.mpr hb2
  have he := pairMean_mono ha hb (fun x y=>mul_le_mul_of_nonneg_right
    (pair_density_variance_lower ha hb hu x y) (sq_nonneg (pairGrad₁ b p r y)))
  simp only [pairMean_mul] at he
  have h₁ : pairMean a b (fun _ y=>(pairGrad₁ b p r y)^2)=p^2+(1-b^2)*r^2 :=
    pair_gradient_square a b p r
  rw [h₁] at he
  have h₂ : pairMean a b (fun x y=>pairDensity a b u x y*pairVariance a u y*(pairGrad₁ b p r y)^2)=
      pairInterMean a b u (fun _x y=>pairVariance a u y*(pairGrad₁ b p r y)^2) := by
    unfold pairInterMean
    congr 1
    funext x y
    ring
  rw [h₂] at he
  have h₃ : (1-a^2)*(1-b^2)*p^2 ≤ (1-a^2)*p^2 := by
    have hh := mul_le_mul_of_nonneg_right (show 1-b^2 ≤ 1 by linarith [sq_nonneg b])
      (mul_nonneg hA (sq_nonneg p))
    nlinarith only [hh]
  have h₄ : 0 ≤ (1-a^2)*(1-b^2)*r^2 := mul_nonneg (mul_nonneg hA hB) (sq_nonneg r)
  nlinarith only [he,h₃,h₄]

lemma pairInterMean_swap (a b u : ℝ) (F : Bool→Bool→ℝ) :
    pairInterMean a b u F=pairInterMean b a u (fun x y=>F y x) := by
  unfold pairInterMean
  rw [pairMean_swap]
  congr 1
  funext x y
  unfold pairDensity
  have he : (1+u*spinValue y*spinValue x)/(1+u*a*b)=
      (1+u*spinValue x*spinValue y)/(1+u*b*a) := by congr 1 <;> ring
  rw [he]

lemma pair_second_energy_lower {a b u s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    (1-a^2)*(1-b^2)*s^2/32 ≤
      pairInterMean a b u (fun x _y=>pairVariance b u x*(pairGrad₂ a s r x)^2) := by
  rw [pairInterMean_swap]
  simpa only [mul_comm (1-a^2) (1-b^2),pairGrad₁,pairGrad₂] using
    (pair_energy_lower (p:=s) (r:=r) hb ha hu)

lemma pairInterMean_add (a b u : ℝ) (F G : Bool→Bool→ℝ) :
    pairInterMean a b u (fun x y=>F x y+G x y)=pairInterMean a b u F+pairInterMean a b u G := by
  unfold pairInterMean
  simp_rw [mul_add]
  exact pairMean_add a b _ _

lemma pairInterMean_nonneg {a b u : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4)
    {F : Bool→Bool→ℝ} (hF : ∀ x y,0 ≤ F x y) : 0 ≤ pairInterMean a b u F := by
  have hh := pairMean_mono ha hb (fun x y=>mul_nonneg (pair_density_nonneg ha hb hu x y) (hF x y))
  have he : pairMean a b (fun _ _=>(0:ℝ))=0 := by simp [pairMean]
  rwa [he] at hh

lemma pair_signed_bound {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    -u*pairInterMean a b u (fun x y=>pairVariance a u y*pairGrad₁ b p r y*
        (pairVariance b u x*pairGrad₂ a s r x))-
      400000*u^2*pairInterMean a b u (fun x y=>|pairVariance a u y*pairGrad₁ b p r y*
        (pairVariance b u x*pairGrad₂ a s r x)|)-
      400000*u^4*pairInterMean a b u (fun x y=>pairVariance a u y*(pairGrad₁ b p r y)^2+
        pairVariance b u x*(pairGrad₂ a s r x)^2) ≤
    pairInterMean a b u (fun x y=>pairResidual a u x y*pairGrad₁ b p r y*
      (pairResidual b u y x*pairGrad₂ a s r x)) := by
  have hu' : |u| ≤ 1/4 := by linarith only [hu]
  let q := pairMean a b (fun x y=>|pairGrad₁ b p r y*pairGrad₂ a s r x|)
  let z := pairMean a b (fun x y=>pairRationalWeight a b u (spinValue x) (spinValue y)*
    (pairGrad₁ b p r y*pairGrad₂ a s r x))
  have hq : |p*s| ≤ q := by
    have hh := abs_pairMean_le ha hb (fun x y=>pairGrad₁ b p r y*pairGrad₂ a s r x)
    change |pairMean a b (fun x y=>(p+r*(spinValue y-b))*(s+r*(spinValue x-a)))| ≤ q at hh
    rwa [pair_gradient_mean] at hh
  have hl := pair_signed_cross_lower (r:=r) ha hb hu hq (pair_weighted_error ha hb hu')
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hb2 : b^2 ≤ 1 := by nlinarith only [sq_abs b,abs_nonneg b,hb]
  have hAB : 0 ≤ (1-a^2)*(1-b^2) := mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2)
  have hl' := mul_le_mul_of_nonneg_left hl hAB
  have hc := pair_abs_cost_lower (p:=p) (s:=s) (r:=r) ha hb hu'
  have h₁ := pair_energy_lower (p:=p) (r:=r) ha hb hu'
  have h₂ := pair_second_energy_lower (s:=s) (r:=r) ha hb hu'
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 1282*256*u^2 by positivity)
  have he' := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (show 0 ≤ 128*u^4 by positivity)
  have habs : 0 ≤ pairInterMean a b u (fun x y=>|pairVariance a u y*pairGrad₁ b p r y*
        (pairVariance b u x*pairGrad₂ a s r x)|) := pairInterMean_nonneg ha hb hu' (fun _ _=>abs_nonneg _)
  have hener : 0 ≤ pairInterMean a b u (fun x y=>pairVariance a u y*(pairGrad₁ b p r y)^2+
        pairVariance b u x*(pairGrad₂ a s r x)^2) := pairInterMean_nonneg ha hb hu'
    (fun x y=>add_nonneg (mul_nonneg (pair_variance_nonneg ha hu' y) (sq_nonneg _))
      (mul_nonneg (pair_variance_nonneg hb hu' x) (sq_nonneg _)))
  have hc'' := mul_nonneg (sq_nonneg u) habs
  have he'' := mul_nonneg (show 0 ≤ u^4 by positivity) hener
  rw [pairInterMean_add] at he'' ⊢
  rw [pair_cross_exact ha hb hu',pair_weighted_product]
  change -u*((1-a^2)*(1-b^2)*z)-_ -_ ≤ _
  change -1282*u^2*q-4*u^4*(p^2+s^2) ≤ pairCrossPolynomial a b u p s r+u*z at hl
  change (1-a^2)*(1-b^2)*(-1282*u^2*q-4*u^4*(p^2+s^2)) ≤
    (1-a^2)*(1-b^2)*(pairCrossPolynomial a b u p s r+u*z) at hl'
  change 1282*256*u^2*((1-a^2)*(1-b^2)*q/256) ≤ _ at hc'
  nlinarith only [hl',hc',he',hc'',he'']
end SKGap

end
end

end OAI
