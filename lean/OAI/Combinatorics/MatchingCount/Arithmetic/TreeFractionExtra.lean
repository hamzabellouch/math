import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreeFractionCosts
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostTactic

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

def sub (x : Fraction×Fraction) : Fraction :=
  normalize (x.1.1*x.2.2-x.2.1*x.1.2,x.1.2*x.2.2)
def subRealizer : Realizer sub := composition
  (pair (composition (pair (composition (pair first.fst second.snd) multiply)
    (composition (pair second.fst first.snd) multiply)) TreeTyped.subtract)
    (composition (pair first.snd second.snd) multiply)) normalizeRealizer
lemma polynomial_sub : PolynomialTime subRealizer := by
  unfold subRealizer Realizer.fst Realizer.snd
  apply polynomial_composition _ polynomial_normalize
  tree_cost
lemma sub_val (x y : Fraction) (hx : 0<x.2) (hy : 0<y.2) (h : val y≤val x) :
    val (sub (x,y))=val x-val y := by
  have hxy : y.1*x.2≤x.1*y.2 := by
    rw [val,val,div_le_div_iff₀ (by exact_mod_cast hy) (by exact_mod_cast hx)] at h
    exact_mod_cast h
  rw [sub,normalize_val]
  simp only [val,Nat.cast_sub hxy,Nat.cast_mul]
  rw [div_sub_div (x.1:ℚ) (y.1:ℚ) (by exact_mod_cast hx.ne') (by exact_mod_cast hy.ne')]
  ring
lemma mul_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    mul (repr x,repr y)=repr (x*y) := by
  have h:=mul_val (repr x) (repr y)
  rw [val_repr hx,val_repr hy] at h
  unfold mul at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma div_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    div (repr x,repr y)=repr (x/y) := by
  have h:=div_val (repr x) (repr y)
  rw [val_repr hx,val_repr hy] at h
  unfold div at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma sub_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) (hxy : y≤x) :
    sub (repr x,repr y)=repr (x-y) := by
  have h:=sub_val (repr x) (repr y) x.pos y.pos (by simpa only [val_repr hx,val_repr hy] using hxy)
  rw [val_repr hx,val_repr hy] at h
  unfold sub at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma height_mul (a b : Fraction) : height (mul (a,b))≤height a+height b+1 := by
  have hn:=normalize_size_num (a.1*b.1,a.2*b.2)
  have hd:=normalize_size_den (a.1*b.1,a.2*b.2)
  have hm:=nat_size_mul a.1 b.1
  have hm':=nat_size_mul a.2 b.2
  have ha:=le_max_left a.1.size a.2.size
  have ha':=le_max_right a.1.size a.2.size
  have hb:=le_max_left b.1.size b.2.size
  have hb':=le_max_right b.1.size b.2.size
  dsimp only at hn hd
  change (mul (a,b)).1.size≤_ at hn
  change (mul (a,b)).2.size≤_ at hd
  unfold height
  apply max_le <;> omega
lemma fractionProduct_height (xs : List Fraction) (a : Fraction) (M : ℕ)
    (hx : ∀ b∈xs,height b≤M) :
    height (xs.foldl (fun a b=>mul (b,a)) a)≤height a+xs.length*(M+1) := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    have hh:=height_mul b a
    have hb:=hx b (by simp)
    have ht:=ih (mul (b,a)) (fun c h=>hx c (by simp [h]))
    simp only [List.foldl_cons,List.length_cons]
    nlinarith
lemma polynomial_fractionProduct : PolynomialTime (fold mulRealizer) := by
  apply polynomial_fold polynomial_mul (8*X+8*X*(X+1)+3)
  intro xs a pre post he
  let S:=weight (xs,a)
  have hpre : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (weight_fst (xs,a)))
  have hb : ∀ b∈pre,height b≤S := by
    intro b hb
    exact (height_le_weight b).trans ((weight_mem (as:=xs) (by simp [he,hb])).trans (weight_fst (xs,a)))
  have ha : height a≤S := (height_le_weight a).trans (weight_snd (xs,a))
  have hh:=fractionProduct_height pre a S hb
  have hw:=weight_le_height (pre.foldl (fun a b=>mul (b,a)) a)
  have hm:=Nat.mul_le_mul_right (S+1) hpre
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change _≤8*S+8*S*(S+1)+3
  nlinarith

def product (xs : List Fraction) : Fraction := xs.foldl (fun a b=>mul (b,a)) (1,1)
def productRealizer : Realizer product :=
  (composition (pair identity (constant (1,1))) (fold mulRealizer)).congr (fun _=>rfl)
lemma polynomial_product : PolynomialTime productRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant _)) polynomial_fractionProduct)
end MatchingFPRAS.TreeFraction

end OAI
