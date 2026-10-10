import OAI.Dynamics.StandardMap.BandIntensity

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Classical
namespace StandardMapEntropy
noncomputable def dyadicZoom (j:ℤ) (s:DyadicTime) : DyadicTime := match j with
  | .ofNat n => (2^n) • s
  | .negSucc n => dyadicFine (n+1) s
lemma dyadicZoom_val (j:ℤ) (s:DyadicTime) : (dyadicZoom j s:ℝ)=(2:ℝ)^j*(s:ℝ) := by
  cases j with
  | ofNat n => simp only [dyadicZoom,AddSubgroup.coe_nsmul,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,Int.ofNat_eq_natCast,zpow_natCast]
  | negSucc n =>
    rw [dyadicZoom,dyadicFine_val,Int.negSucc_eq,zpow_neg,zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_natCast,zpow_one,pow_succ]
    ring
lemma dyadicZoom_zero (j:ℤ) : dyadicZoom j 0=0 := by apply Subtype.ext; simp only [dyadicZoom_val,ZeroMemClass.coe_zero,mul_zero]
lemma dyadicZoom_add (j:ℤ) (s t:DyadicTime) : dyadicZoom j (s+t)=dyadicZoom j s+dyadicZoom j t := by
  apply Subtype.ext; simp only [dyadicZoom_val,AddSubgroup.coe_add,mul_add]
lemma dyadicZoom_succ (j:ℤ) (s:DyadicTime) : dyadicZoom (j+1) s=dyadicZoom j (s+s) := by
  apply Subtype.ext; simp only [dyadicZoom_val,AddSubgroup.coe_add,zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_one]; ring
lemma dyadicZoom_pred (j:ℤ) (s:DyadicTime) : dyadicZoom (j-1) s=dyadicZoom j (dyadicHalf s) := by
  apply Subtype.ext; simp only [dyadicZoom_val,dyadicHalf_val,zpow_sub₀ (by norm_num : (2:ℝ)≠0),zpow_one]; ring
lemma dyadicZoom_two (j:ℤ) : dyadicZoom j (dyadicInt 2)=dyadicZoom (j+1) (dyadicInt 1) := by
  rw [dyadicZoom_succ]; congr 1; apply Subtype.ext; norm_num
lemma scaleZ_eval (j:ℤ) (d:NonAffineArray) (hu:UnitArray d.val) (s t:DyadicTime) :
    (scaleZ j d).val.val s t=d.val.val (dyadicZoom j s) (dyadicZoom j t)/(2:ℝ)^j := by
  induction j using Int.induction_on generalizing s t with
  | zero => simp only [scaleZ_zero,dyadicZoom,pow_zero,one_nsmul,zpow_zero,div_one]
  | succ j ih =>
    rw [add_comm,scaleZ_add,scaleZ_one,nonaffineDouble,ite_eq_left ((scaleZ_unit j d).mpr hu)]
    change (scaleZ j d).val.val (s+s) (t+t)/2=_
    rw [ih,←dyadicZoom_succ,←dyadicZoom_succ,zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_one]
    ring_nf
  | pred j ih =>
    rw [sub_eq_add_neg,add_comm,scaleZ_add,scaleZ_neg_one,nonaffineHalf,dite_eq_left ((scaleZ_unit (-(j:ℤ)) d).mpr hu)]
    change 2*(scaleZ (-(j:ℤ)) d).val.val (dyadicHalf s) (dyadicHalf t)=_
    rw [ih,←dyadicZoom_pred,←dyadicZoom_pred]
    rw [zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_neg_one]
    ring_nf
lemma scaleZ_shortfall (j:ℤ) (d:NonAffineArray) (hu:UnitArray d.val) (s t:DyadicTime) :
    arrayShortfall s t (scaleZ j d).val=arrayShortfall (dyadicZoom j s) (dyadicZoom j t) d.val := by
  unfold arrayShortfall
  rw [scaleZ_eval j d hu,dyadicZoom_val,dyadicZoom_val,←mul_sub,div_div]
lemma scaleZ_capG (α:ℝ) (j:ℤ) (d:NonAffineArray) (hu:UnitArray d.val) :
    capG α (scaleZ j d).val=entropyCap α (arrayShortfall 0 (dyadicZoom (j+1) (dyadicInt 1)) d.val)-
      (entropyCap α (arrayShortfall 0 (dyadicZoom j (dyadicInt 1)) d.val)+entropyCap α (arrayShortfall (dyadicZoom j (dyadicInt 1)) (dyadicZoom (j+1) (dyadicInt 1)) d.val))/2 := by
  unfold capG
  rw [scaleZ_shortfall j d hu,scaleZ_shortfall j d hu,scaleZ_shortfall j d hu,dyadicZoom_zero,dyadicZoom_two]
end StandardMapEntropy

end OAI
