import Mathlib
import OAI.Combinatorics.Chromatic.Walls.WallUnits
import OAI.Combinatorics.Chromatic.Walls.RationalFiberReciprocal

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K : Type*} [Field K]

def scaleAction (v : Kˣ) : Multiplicative ℤ →* MulAut (RatFunc K)ˣ where
  toFun t:=Units.mapEquiv (scaleEquiv (v^(-2*t.toAdd))).toMulEquiv
  map_one':=by
    ext x
    change scale (v^(-2*(0:ℤ))) (x:RatFunc K)=(x:RatFunc K)
    simp
  map_mul' t u:=by
    ext x
    change scale (v^(-2*(t.toAdd+u.toAdd))) (x:RatFunc K)=
      scale (v^(-2*t.toAdd)) (scale (v^(-2*u.toAdd)) (x:RatFunc K))
    rw [show v^(-2*(t.toAdd+u.toAdd))=v^(-2*t.toAdd)*v^(-2*u.toAdd) by rw [mul_add,zpow_add],←scale_mul]
    rfl
@[simp] lemma scaleAction_val (v : Kˣ) (t : Multiplicative ℤ) (a : (RatFunc K)ˣ) :
    ((scaleAction v t a : (RatFunc K)ˣ):RatFunc K)=scale (v^(-2*t.toAdd)) (a:RatFunc K) := rfl
lemma linearFactor_ne_zero (a : K) : (1+RatFunc.C a*RatFunc.X : RatFunc K)≠0 := by
  have he : (1+RatFunc.C a*RatFunc.X : RatFunc K)=
      algebraMap (Polynomial K) (RatFunc K) (1+Polynomial.C a*Polynomial.X) := by simp
  rw [he]
  intro hz
  have h : (1+Polynomial.C a*Polynomial.X : Polynomial K)=0 :=
    (RatFunc.algebraMap_injective (K:=K)) (by simpa using hz)
  have H:=congrArg (Polynomial.coeff · 0) h
  simp at H

def pureStep (v : Kˣ) : (RatFunc K)ˣ := Units.mk0 _ (linearFactor_ne_zero (↑(v⁻¹):K))
abbrev PureExtension (v : Kˣ) := (RatFunc K)ˣ ⋊[scaleAction v] Multiplicative ℤ
def pureGenerator (v : Kˣ) : PureExtension v := ⟨pureStep v,Multiplicative.ofAdd 1⟩
def pureRatio (v : Kˣ) (t : ℤ) : (RatFunc K)ˣ := (pureGenerator v^t).left
lemma pureRight (v : Kˣ) (t : ℤ) : (pureGenerator v^t).right=Multiplicative.ofAdd t := by
  change SemidirectProduct.rightHom (pureGenerator v^t)=_
  rw [map_zpow]
  change (Multiplicative.ofAdd 1)^t=Multiplicative.ofAdd t
  rw [←ofAdd_zsmul,smul_eq_mul,mul_one]
@[simp] lemma pureRatio_zero (v : Kˣ) : pureRatio v 0=1 := by simp [pureRatio]
@[simp] lemma pureRatio_one (v : Kˣ) : pureRatio v 1=pureStep v := by simp [pureRatio,pureGenerator]
lemma pureRatio_add (v : Kˣ) (t u : ℤ) :
    pureRatio v (t+u)=pureRatio v t*scaleAction v (Multiplicative.ofAdd t) (pureRatio v u) := by
  simp only [pureRatio,zpow_add,SemidirectProduct.mul_left,pureRight]
lemma pureRatio_nat (v : Kˣ) (n : ℕ) :
    pureRatio v (n:ℤ)=∏i∈Finset.range n,scaleAction v (Multiplicative.ofAdd (i:ℤ)) (pureStep v) := by
  induction n with
  | zero=>simp
  | succ n ih=>rw [Nat.cast_add,Nat.cast_one,pureRatio_add,pureRatio_one,ih,Finset.prod_range_succ]
lemma pureRatio_nat_val (v : Kˣ) (n : ℕ) :
    (pureRatio v (n:ℤ):RatFunc K)=
      ∏i∈Finset.range n,(1+RatFunc.C (↑(v^(-2*(i:ℤ)-1)):K)*RatFunc.X) := by
  rw [pureRatio_nat,Units.coe_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [scaleAction_val]
  change scale (v^(-2*(i:ℤ))) (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X)=_
  rw [map_add,map_one,map_mul,scale_constant,scale_X,←mul_assoc,←map_mul,
    ←Units.val_mul,←zpow_neg_one,←zpow_add]
  congr 3
  ring_nf
lemma pureRatio_neg (v : Kˣ) (t : ℤ) :
    scaleAction v (Multiplicative.ofAdd t) (pureRatio v (-t))=(pureRatio v t)⁻¹ := by
  apply mul_left_cancel (a:=pureRatio v t)
  rw [←pureRatio_add,add_neg_cancel,pureRatio_zero,mul_inv_cancel]
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open WallUnits PowerSeries
noncomputable section
variable {K : Type*} [Field K]
variable (v : Kˣ)
def shiftedElementary (t : ℤ) : PowerSeries K :=
  rescale (↑(v^(-2*t)):K) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))
lemma shiftedElementary_zero : shiftedElementary v 0=
    elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K) := by
  simp [shiftedElementary]
lemma shiftedElementary_constant (t : ℤ) : constantCoeff (shiftedElementary v t)=1 := by
  rw [shiftedElementary,←coeff_zero_eq_constantCoeff,coeff_rescale]
  simp [elementaryCoeff]
lemma shiftedElementary_step
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (t : ℤ) :
    shiftedElementary v t=(1+C (↑(v^(-2*t-1)):K)*X)*shiftedElementary v (t+1) := by
  conv_lhs => rw [shiftedElementary,elementary_tail _ _ hq]
  rw [_root_.map_mul,_root_.map_add,_root_.map_one,_root_.map_mul,rescale_C,rescale_X,rescale_rescale]
  rw [←mul_assoc,←(PowerSeries.C (R:=K)).map_mul,←Units.val_mul,←zpow_neg_one,←zpow_add]
  have H1 : -1+(-2*t)= -2*t-1:=by ring
  rw [H1]
  unfold shiftedElementary
  simp only [zpow_neg_one]
  congr 2
  rw [←Units.val_mul,←zpow_add]
  congr 2
  ring_nf
lemma expandedPure_step (t : ℤ) :
    expandZero (pureRatio v (t+1):RatFunc K)=
      expandZero (pureRatio v t:RatFunc K)*
        HahnSeries.ofPowerSeries ℤ K (1+C (↑(v^(-2*t-1)):K)*X) := by
  rw [pureRatio_add,Units.val_mul,pureRatio_one,scaleAction_val]
  change expandZero ((pureRatio v t:RatFunc K)*
    scale (v^(-2*t)) (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X))=_
  rw [_root_.map_add,_root_.map_one,_root_.map_mul,_root_.map_mul,scale_constant,scale_X,
    ←mul_assoc,←RatFunc.C.map_mul,←Units.val_mul,←zpow_neg_one,←zpow_add]
  rw [show -1+(-2*t)= -2*t-1 by ring]
  simp only [_root_.map_mul,_root_.map_add,_root_.map_one,expandZero_constant,
    expandZero_X,HahnSeries.ofPowerSeries_C,HahnSeries.ofPowerSeries_X]
lemma expandedPure_times_shift
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (t : ℤ) :
    expandZero (pureRatio v t:RatFunc K)*
      HahnSeries.ofPowerSeries ℤ K (shiftedElementary v t)=
        HahnSeries.ofPowerSeries ℤ K (shiftedElementary v 0) := by
  induction t using Int.induction_on with
  | zero=>simp
  | succ t ih=>
    rw [expandedPure_step,mul_assoc,←_root_.map_mul,←shiftedElementary_step v hq]
    exact ih
  | pred t ih=>
    rw [shiftedElementary_step v hq (-↑t-1)]
    have H : (-↑t-1)+(1:ℤ)= -↑t:=by ring
    rw [H,_root_.map_mul,←mul_assoc,←expandedPure_step,H]
    exact ih
lemma ofPowerSeries_inv_constant_one (f : PowerSeries K) (hf : constantCoeff f=1) :
    HahnSeries.ofPowerSeries ℤ K f⁻¹=(HahnSeries.ofPowerSeries ℤ K f)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [←_root_.map_mul,PowerSeries.inv_mul_cancel f (by rw [hf]; exact one_ne_zero),_root_.map_one]
lemma expandedPure_ratio
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (t : ℤ) :
    expandZero (pureRatio v t:RatFunc K)=HahnSeries.ofPowerSeries ℤ K
      (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K)*(shiftedElementary v t)⁻¹) := by
  have H:=expandedPure_times_shift v hq t
  have H0 : HahnSeries.ofPowerSeries ℤ K (shiftedElementary v t)≠0 := by
    intro h
    have he:shiftedElementary v t=0:=HahnSeries.ofPowerSeries_injective (Γ:=ℤ)
      (by simpa only [_root_.map_zero] using h)
    have hc:=congrArg constantCoeff he
    rw [shiftedElementary_constant,_root_.map_zero] at hc
    exact one_ne_zero hc
  rw [shiftedElementary_zero] at H
  rw [_root_.map_mul,ofPowerSeries_inv_constant_one _ (shiftedElementary_constant v t)]
  calc
    _ = (expandZero (pureRatio v t:RatFunc K)*
      HahnSeries.ofPowerSeries ℤ K (shiftedElementary v t))*
        (HahnSeries.ofPowerSeries ℤ K (shiftedElementary v t))⁻¹ := by
      rw [mul_assoc,mul_inv_cancel₀ H0,mul_one]
    _ = _ := by rw [H]
end
end ElementaryPositivity.RationalFiber

end

end OAI
