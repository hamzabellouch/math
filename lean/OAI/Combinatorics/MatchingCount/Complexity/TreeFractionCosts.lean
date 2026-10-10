import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeCategorical
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialGrid

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

def height (x : Fraction) : ℕ := max x.1.size x.2.size
lemma height_le_weight (x : Fraction) : height x≤weight x := by
  rcases x with ⟨a,b⟩
  have ha:=size_le_weight a
  have hb:=size_le_weight b
  simp only [height,weight_prod]
  exact max_le (by omega) (by omega)
lemma weight_le_height (x : Fraction) : weight x≤8*height x+3 := by
  rcases x with ⟨a,b⟩
  have ha:=weight_nat_le a
  have hb:=weight_nat_le b
  have h1:=le_max_left a.size b.size
  have h2:=le_max_right a.size b.size
  simp only [height,weight_prod]
  omega
lemma height_add (a b : Fraction) : height (add (a,b))≤height a+height b+2 := by
  have hn:=normalize_size_num (a.1*b.2+b.1*a.2,a.2*b.2)
  have hd:=normalize_size_den (a.1*b.2+b.1*a.2,a.2*b.2)
  have hs:=nat_size_add (a.1*b.2) (b.1*a.2)
  have hm:=nat_size_mul a.1 b.2
  have hm':=nat_size_mul b.1 a.2
  have hm'':=nat_size_mul a.2 b.2
  have ha:=le_max_left a.1.size a.2.size
  have ha':=le_max_right a.1.size a.2.size
  have hb:=le_max_left b.1.size b.2.size
  have hb':=le_max_right b.1.size b.2.size
  dsimp only at hn hd
  change (add (a,b)).1.size≤_ at hn
  change (add (a,b)).2.size≤_ at hd
  unfold height
  apply max_le <;> omega
lemma fractionFold_height (xs : List Fraction) (a : Fraction) (M : ℕ)
    (hx : ∀ b∈xs,height b≤M) :
    height (xs.foldl (fun a b=>add (b,a)) a)≤height a+xs.length*(M+2) := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    have hh:=height_add b a
    have hb:=hx b (by simp)
    have ht:=ih (add (b,a)) (fun c h=>hx c (by simp [h]))
    simp only [List.foldl_cons,List.length_cons]
    nlinarith
lemma polynomial_fractionFold : PolynomialTime (fold addRealizer) := by
  apply polynomial_fold polynomial_add (8*X+8*X*(X+2)+3)
  intro xs a pre post he
  let S:=weight (xs,a)
  have hpre : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (weight_fst (xs,a)))
  have hb : ∀ b∈pre,height b≤S := by
    intro b hb
    exact (height_le_weight b).trans ((weight_mem (as:=xs) (by simp [he,hb])).trans (weight_fst (xs,a)))
  have ha : height a≤S := (height_le_weight a).trans (weight_snd (xs,a))
  have hh:=fractionFold_height pre a S hb
  have hw:=weight_le_height (pre.foldl (fun a b=>add (b,a)) a)
  have hm:=Nat.mul_le_mul_right (S+2) hpre
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change _≤8*S+8*S*(S+2)+3
  nlinarith
lemma polynomial_sum : PolynomialTime sumRealizer := by
  unfold sumRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant _)) polynomial_fractionFold
end MatchingFPRAS.TreeFraction

end OAI
