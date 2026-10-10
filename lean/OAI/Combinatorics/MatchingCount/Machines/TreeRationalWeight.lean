import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.TreeCycleTable

namespace OAI

namespace MatchingFPRAS.TreeFraction
lemma fold_product_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) (a : ℚ) (ha : 0≤a) :
    ((xs.map repr).foldl (fun a b=>mul (b,a)) (repr a))=repr (xs.prod*a) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have h : 0≤x:=hx x (by simp)
    simp only [List.map_cons,List.foldl_cons,mul_repr h ha]
    rw [ih (fun y hy=>hx y (by simp [hy])) (x*a) (mul_nonneg h ha)]
    congr 1
    simp only [List.prod_cons]
    ring
lemma product_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) : product (xs.map repr)=repr xs.prod := by
  unfold product
  have h:=fold_product_repr xs hx 1 (by decide)
  simpa only [mul_one,show repr (1:ℚ)=(1,1) from rfl] using h
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped TreeFraction

variable {E C : Type} [Codec E] [Codec C] [LinearOrder E]
attribute [local instance] Transport.Sparse.finsetOrder

def weight (w : C×E→Fraction) (x : C×Finset E) : Fraction :=
  product ((x.2.sort (·≤·)).map (fun e=>w (x.1,e)))
def weightRealizer {w : C×E→Fraction} (W : Realizer w) : Realizer (weight w) :=
  (composition (composition (pair first (composition second finsetList)) (mapWith W)) productRealizer).congr (fun _=>rfl)
lemma polynomial_weight {w : C×E→Fraction} {W : Realizer w} (hW : PolynomialTime W) :
    PolynomialTime (weightRealizer W) := by
  unfold weightRealizer
  apply polynomial_congr
  have := polynomial_product
  tree_cost

def pairWeight (w z : C×E→Fraction) (x : C×PairState E) : Fraction :=
  mul (weight w (x.1,x.2.1),weight z (x.1,x.2.2))
def pairWeightRealizer {w z : C×E→Fraction} (W : Realizer w) (Z : Realizer z) : Realizer (pairWeight w z) :=
  (composition (pair (composition (pair first second.fst) (weightRealizer W))
    (composition (pair first second.snd) (weightRealizer Z))) mulRealizer).congr (fun _=>rfl)
lemma polynomial_pairWeight {w z : C×E→Fraction} {W : Realizer w} {Z : Realizer z}
    (hW : PolynomialTime W) (hZ : PolynomialTime Z) : PolynomialTime (pairWeightRealizer W Z) := by
  unfold pairWeightRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_mul
  have := polynomial_weight hW
  have := polynomial_weight hZ
  tree_cost

variable (w : C×E→Fraction) (c : C) (q : E→ℚ) (hq : ∀ e,0≤q e)
    (hw : ∀ e,w (c,e)=TreeFraction.repr (q e))
omit [Codec E] [Codec C] in
include hq hw in
lemma weight_repr (s : Finset E) : weight w (c,s)=TreeFraction.repr (∏ e∈s,q e) := by
  unfold weight
  dsimp only
  simp only [hw]
  change product ((s.sort (·≤·)).map (TreeFraction.repr ∘ q))=_
  rw [←List.map_map,product_repr _ (by intro a ha; obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha; exact hq b)]
  congr 1
  simpa only [Finset.sort_toFinset] using (List.prod_toFinset q (Finset.sort_nodup s (·≤·))).symm

variable [Fintype E] {V : Type} [Fintype V] [DecidableEq V] (ends : E→Sym2 V)
omit [Codec E] [Codec C] [Fintype E] [DecidableEq V] in
lemma pairWeight_repr (w z : C×E→Fraction) (c : C) (q r : E→ℚ) (hq : ∀ e,0≤q e) (hr : ∀ e,0≤r e)
    (hw : ∀ e,w (c,e)=TreeFraction.repr (q e)) (hz : ∀ e,z (c,e)=TreeFraction.repr (r e))
    (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e)) :
    pairWeight w z (c,pairRepr ends a)=TreeFraction.repr (Transport.Sparse.rationalPairWeight ends q r a) := by
  unfold pairWeight pairRepr
  rw [weight_repr w c q hq hw,weight_repr z c r hr hz,mul_repr (Finset.prod_nonneg (fun e _=>hq e))
    (Finset.prod_nonneg (fun e _=>hr e))]
  rfl
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
