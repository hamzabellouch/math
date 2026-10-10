import OAI.Probability.GaussianPropeller.CapCertificates

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.FourAlgebra
open scoped RealInnerProductSpace

lemma quartic_positive {t L c₀ c₁ c₂ c₄:ℝ} (ht:0≤t) (htL:t≤L) (hL:0<L)
    (hc₄:0≤c₄) (hconc:c₂+3*c₄*L^2≤0) (hc₀:0<c₀)
    (hend:0<c₀+c₁*L+c₂*L^2+c₄*L^4) : 0<c₀+c₁*t+c₂*t^2+c₄*t^4 := by
  have ht2 : t^2≤L^2 := (sq_le_sq₀ ht hL.le).mpr htL
  have htL' : L*t≤L^2 := by nlinarith only [mul_le_mul_of_nonneg_left htL hL.le]
  have hb : 0≤-c₂-c₄*(t^2+L*t+L^2) := by
    have hh := mul_le_mul_of_nonneg_left (show t^2+L*t+L^2≤3*L^2 by linarith only [ht2,htL']) hc₄
    linarith only [hh,hconc]
  have hp:=mul_nonneg (mul_nonneg ht (sub_nonneg.mpr htL)) hb
  have hid : L*(c₀+c₁*t+c₂*t^2+c₄*t^4) =
      (L-t)*c₀+t*(c₀+c₁*L+c₂*L^2+c₄*L^4)+L*(t*(L-t)*(-c₂-c₄*(t^2+L*t+L^2))) := by ring
  have hlin : 0<(L-t)*c₀+t*(c₀+c₁*L+c₂*L^2+c₄*L^4) := by
    by_cases htz:t=0
    · subst t; simpa using mul_pos hL hc₀
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr htL) hc₀.le)
        (mul_pos (lt_of_le_of_ne ht (Ne.symm htz)) hend)
  have hm:=mul_nonneg hL.le hp
  nlinarith only [hid,hlin,hm,hL]

lemma small_numeric_one {t:ℝ} (ht:t∈Set.Icc (0:ℝ) (39/250:ℝ)) :
    4*(150/157:ℝ)^2*t^2*(13/10:ℝ)^4 <
      (1-2*t^2)^2-(10/3:ℝ)*((10003/40000:ℝ)-(83/200:ℝ)*t+(81/250:ℝ)*t^2) := by
  have hh:=quartic_positive (c₀:=(1997/12000:ℝ)) (c₁:=(83/60:ℝ))
    (c₂:=-(9556648/616225:ℝ)) (c₄:=4) ht.1 ht.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith only [hh]

lemma small_numeric_two {t:ℝ} (ht:t∈Set.Icc (0:ℝ) (39/250:ℝ)) :
    4*(150/157:ℝ)^2*t^2*(4/3:ℝ)^4 <
      (1-(14/9:ℝ)*t^2)^2-(10/3:ℝ)*((10003/40000:ℝ)-(83/200:ℝ)*t+(81/250:ℝ)*t^2) := by
  have hh:=quartic_positive (c₀:=(1997/12000:ℝ)) (c₁:=(83/60:ℝ))
    (c₂:=-(87244007/5546025:ℝ)) (c₄:=(196/81:ℝ)) ht.1 ht.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith only [hh]

lemma pair_product {a b B:ℝ} (ha:0≤a) (hb:0≤b) (hab:a+b≤B) :
    (1+a)^2*(1+b)^2≤(1+B/2)^4 := by
  have hB:0≤B := (add_nonneg ha hb).trans hab
  have hh : (1+a)*(1+b)≤(1+B/2)^2 := by
    have hs:(a+b)^2≤B^2 := (sq_le_sq₀ (add_nonneg ha hb) hB).mpr hab
    nlinarith only [hs,hab,sq_nonneg (a-b)]
  have hq:((1+a)*(1+b))^2≤((1+B/2)^2)^2 :=
    (sq_le_sq₀ (by positivity) (sq_nonneg _)).mpr hh
  nlinarith only [hq]

lemma small_core {t a b c H V D:ℝ} (ht:t∈Set.Icc (0:ℝ) (39/250:ℝ))
    (ha:0≤a) (hb:0≤b) (hc:0≤c) (hs:a+b+c=1) (hac:a≤c) (hbc:b≤c)
    (hH:H=1-t^2-(a^2+b^2+c^2)*t^2)
    (hV:(3/5:ℝ)*V≤(10003/40000:ℝ)-(83/200:ℝ)*t+(81/250:ℝ)*t^2)
    (hD:4*D=H^2-2*V)
    (hpair:D≤(3/Real.pi)^2*t^2*(1+a)^2*(1+b)^2) : False := by
  have hk : (3/Real.pi)^2≤(150/157:ℝ)^2 := by
    apply (sq_le_sq₀ (by positivity) (by norm_num)).mpr
    rw [div_le_iff₀ Real.pi_pos]
    have hp:=Real.pi_gt_d2
    linarith only [hp]
  have hab : a+b≤2/3 := by linarith only [hac,hbc,hs]
  have ht2 : t^2≤(39/250:ℝ)^2 := (sq_le_sq₀ ht.1 (by norm_num)).mpr ht.2
  have hcoef : a^2+b^2+c^2≤1 := by
    nlinarith only [hs,mul_nonneg ha hb,mul_nonneg ha hc,mul_nonneg hb hc]
  have hpair' : D≤(150/157:ℝ)^2*t^2*(1+a)^2*(1+b)^2 := hpair.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hk (sq_nonneg t)) (sq_nonneg (1+a))) (sq_nonneg (1+b)))
  by_cases hsmall : a+b≤3/5
  · have hprod := pair_product ha hb hsmall
    have hd : D≤(150/157:ℝ)^2*t^2*(13/10:ℝ)^4 := by
      have hh:=mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg (150/157:ℝ)) (sq_nonneg t))
      norm_num at hh
      nlinarith only [hpair',hh]
    have hl : 1-2*t^2≤H := by
      have hh:=mul_le_mul_of_nonneg_right hcoef (sq_nonneg t)
      nlinarith only [hh,hH]
    have hl0 : 0≤1-2*t^2 := by nlinarith only [ht2]
    have hsq : (1-2*t^2)^2≤H^2 := (sq_le_sq₀ hl0 (hl0.trans hl)).mpr hl
    have hn:=small_numeric_one ht
    nlinarith only [hV,hD,hd,hsq,hn]
  · have hablo : 3/5≤a+b := (lt_of_not_ge hsmall).le
    have hcoef' : a^2+b^2+c^2≤5/9 := by
      have hh:=mul_nonneg (sub_nonneg.mpr hab) (show 0≤2*(a+b)-2/3 by linarith only [hablo])
      nlinarith only [hs,hh,mul_nonneg ha hb]
    have hprod := pair_product ha hb hab
    have hd : D≤(150/157:ℝ)^2*t^2*(4/3:ℝ)^4 := by
      have hh:=mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg (150/157:ℝ)) (sq_nonneg t))
      norm_num at hh
      nlinarith only [hpair',hh]
    have hl : 1-(14/9:ℝ)*t^2≤H := by
      have hh:=mul_le_mul_of_nonneg_right hcoef' (sq_nonneg t)
      nlinarith only [hh,hH]
    have hl0 : 0≤1-(14/9:ℝ)*t^2 := by nlinarith only [ht2]
    have hsq : (1-(14/9:ℝ)*t^2)^2≤H^2 := (sq_le_sq₀ hl0 (hl0.trans hl)).mpr hl
    have hn:=small_numeric_two ht
    nlinarith only [hV,hD,hd,hsq,hn]

lemma small_exclusion {t a b c H V D:ℝ} (ht:t∈Set.Icc (0:ℝ) (39/250:ℝ))
    (ha:0≤a) (hb:0≤b) (hc:0≤c) (hs:a+b+c=1)
    (hH:H=1-t^2-(a^2+b^2+c^2)*t^2)
    (hV:(3/5:ℝ)*V≤(10003/40000:ℝ)-(83/200:ℝ)*t+(81/250:ℝ)*t^2)
    (hD:4*D=H^2-2*V)
    (hab:D≤(3/Real.pi)^2*t^2*(1+a)^2*(1+b)^2)
    (hac:D≤(3/Real.pi)^2*t^2*(1+a)^2*(1+c)^2)
    (hbc:D≤(3/Real.pi)^2*t^2*(1+b)^2*(1+c)^2) : False := by
  by_cases hac':a≤c
  · by_cases hbc':b≤c
    · exact small_core ht ha hb hc hs hac' hbc' hH hV hD hab
    · apply small_core (a:=a) (b:=c) (c:=b) ht ha hc hb (by linarith only [hs])
        (hac'.trans (le_of_not_ge hbc')) (le_of_not_ge hbc')
        (by nlinarith only [hH]) hV hD hac
  · by_cases hba:b≤a
    · exact small_core (a:=b) (b:=c) (c:=a) ht hb hc ha (by linarith only [hs]) hba
        (le_of_not_ge hac') (by nlinarith only [hH]) hV hD hbc
    · exact small_core (a:=a) (b:=c) (c:=b) ht ha hc hb (by linarith only [hs])
        (le_of_not_ge hba) ((le_of_not_ge hac').trans (le_of_not_ge hba))
        (by nlinarith only [hH]) hV hD hac

end GaussianPropeller.FourAlgebra

end OAI
