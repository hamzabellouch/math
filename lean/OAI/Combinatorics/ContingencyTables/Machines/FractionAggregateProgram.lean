import OAI.Combinatorics.MatchingCount.Complexity.TreeFractionCosts
import OAI.Combinatorics.ContingencyTables.Transport.FiniteIndependentAverages

namespace OAI

/-! # Polynomial exact fraction averages and products

These are the arithmetic folds used by the executed weight estimator.
Normalization makes the average valid on every input, including a raw
fraction with denominator zero.
-/

namespace ContingencyTables.FractionAggregateProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators

def average (xs : List TreeFraction.Fraction) : TreeFraction.Fraction :=
  TreeFraction.div (TreeFraction.sum (xs.map TreeFraction.normalize),(xs.length,1))
def averageRealizer : Realizer average :=
  composition (f := fun xs : List TreeFraction.Fraction =>
    (TreeFraction.sum (xs.map TreeFraction.normalize),(xs.length,1))) (g := TreeFraction.div)
    (pair (composition (map TreeFraction.normalizeRealizer) TreeFraction.sumRealizer)
      (pair listLength (constant 1))) TreeFraction.divRealizer
lemma polynomial_average : PolynomialTime averageRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_map TreeFraction.polynomial_normalize)
      TreeFraction.polynomial_sum)
    (polynomial_pair polynomial_listLength (polynomial_constant 1))) TreeFraction.polynomial_div

lemma average_value (xs : List TreeFraction.Fraction) :
    TreeFraction.val (average xs)=(xs.map TreeFraction.val).sum/(xs.length:ℚ) := by
  rw [average,TreeFraction.div_val,TreeFraction.sum_val]
  · rw [show TreeFraction.val (xs.length,1)=(xs.length:ℚ) by
      simp only [TreeFraction.val,Nat.cast_one,div_one]]
    simp only [List.map_map,Function.comp_def,TreeFraction.normalize_val]
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    exact TreeFraction.normalize_den_pos a

lemma average_ofFn {X : Type*} (g : X → TreeFraction.Fraction) (N : ℕ)
    (draws : Fin N → X) :
    TreeFraction.val (average (List.ofFn (fun i => g (draws i))))=
      (∑ i : Fin N, TreeFraction.val (g (draws i)))/(N:ℚ) := by
  rw [average_value]
  simp only [List.map_ofFn,List.length_ofFn,List.sum_ofFn,Function.comp_apply]

private lemma height_mul (a b : TreeFraction.Fraction) :
    TreeFraction.height (TreeFraction.mul (a,b)) ≤
      TreeFraction.height a+TreeFraction.height b+1 := by
  have hn := TreeFraction.normalize_size_num (a.1*b.1,a.2*b.2)
  have hd := TreeFraction.normalize_size_den (a.1*b.1,a.2*b.2)
  have hnum := nat_size_mul a.1 b.1
  have hden := nat_size_mul a.2 b.2
  have ha := le_max_left a.1.size a.2.size
  have ha' := le_max_right a.1.size a.2.size
  have hb := le_max_left b.1.size b.2.size
  have hb' := le_max_right b.1.size b.2.size
  dsimp only at hn hd
  change (TreeFraction.mul (a,b)).1.size ≤ _ at hn
  change (TreeFraction.mul (a,b)).2.size ≤ _ at hd
  unfold TreeFraction.height
  apply max_le <;> omega

private lemma fold_height (xs : List TreeFraction.Fraction) (a : TreeFraction.Fraction)
    (M : ℕ) (hx : ∀ b∈xs,TreeFraction.height b ≤ M) :
    TreeFraction.height (xs.foldl (fun a b => TreeFraction.mul (b,a)) a) ≤
      TreeFraction.height a+xs.length*(M+1) := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    have hb := hx b (by simp)
    have ht := ih (TreeFraction.mul (b,a)) (fun c hc => hx c (by simp [hc]))
    have hm := height_mul b a
    simp only [List.foldl_cons,List.length_cons]
    nlinarith

private lemma polynomial_productFold : PolynomialTime (fold TreeFraction.mulRealizer) := by
  apply polynomial_fold TreeFraction.polynomial_mul (8*X+8*X*(X+1)+3)
  intro xs a pre post he
  let S := weight (xs,a)
  have hp : pre.length ≤ S :=
    (list_length_le_weight pre).trans ((weight_prefix he).trans (weight_fst (xs,a)))
  have hb : ∀ b∈pre,TreeFraction.height b ≤ S := by
    intro b hb
    exact (TreeFraction.height_le_weight b).trans
      ((weight_mem (as := xs) (by simp [he,hb])).trans (weight_fst (xs,a)))
  have ha : TreeFraction.height a ≤ S :=
    (TreeFraction.height_le_weight a).trans (weight_snd (xs,a))
  have hh := fold_height pre a S hb
  have hw := TreeFraction.weight_le_height (pre.foldl (fun a b => TreeFraction.mul (b,a)) a)
  have hm := Nat.mul_le_mul_right (S+1) hp
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  change _ ≤ 8*S+8*S*(S+1)+3
  nlinarith

def product (xs : List TreeFraction.Fraction) : TreeFraction.Fraction :=
  xs.foldl (fun a b => TreeFraction.mul (b,a)) (1,1)
def productRealizer : Realizer product :=
  composition (f := fun xs : List TreeFraction.Fraction => (xs,(1,1)))
    (g := fun z : List TreeFraction.Fraction×TreeFraction.Fraction =>
      z.1.foldl (fun a b => TreeFraction.mul (b,a)) z.2)
    (pair identity (constant (1,1))) (fold TreeFraction.mulRealizer)
lemma polynomial_product : PolynomialTime productRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant (1,1)))
    polynomial_productFold

private lemma fold_value (xs : List TreeFraction.Fraction) (a : TreeFraction.Fraction) :
    TreeFraction.val (xs.foldl (fun a b => TreeFraction.mul (b,a)) a)=
      TreeFraction.val a*(xs.map TreeFraction.val).prod := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons,ih,TreeFraction.mul_val,List.map_cons,List.prod_cons]
    ring

lemma product_value (xs : List TreeFraction.Fraction) :
    TreeFraction.val (product xs)=(xs.map TreeFraction.val).prod := by
  rw [product,fold_value]
  simp only [TreeFraction.val,Nat.cast_one,div_self (by norm_num : (1:ℚ)≠0),one_mul]

end ContingencyTables.FractionAggregateProgram

end OAI
