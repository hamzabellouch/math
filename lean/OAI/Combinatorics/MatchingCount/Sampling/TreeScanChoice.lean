import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeOptionsFinite
import OAI.Combinatorics.MatchingCount.Machines.TreeLabelTable
import OAI.Combinatorics.MatchingCount.Machines.TreeQuad
import OAI.Combinatorics.MatchingCount.Machines.TreeSum

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped ExecutableOptions

variable {I C : Type} [Codec I] [Codec C] [Inhabited I] [LinearOrder I]
attribute [local instance] Transport.prodOrder Transport.sumOrder
local instance : Inhabited (Replica.Update I) := ⟨Sum.inr default⟩
abbrev ScanSetup (C I : Type) := C×(Finset I×Finset I)

def updateList (g : C×(I×I)→Bool) (x : ScanSetup C I) : List (Replica.Update I) :=
  (((x.2.1.sort (·≤·)).product (x.2.1.sort (·≤·))).filter (fun ij=>g (x.1,ij))).map Sum.inl++
    (x.2.2.sort (·≤·)).map Sum.inr

def updateListRealizer {g : C×(I×I)→Bool} (G : Realizer g) : Realizer (updateList g) := by
  let xs : Realizer (fun x : ScanSetup C I=>x.2.1.sort (·≤·)) := (composition second.fst finsetList).congr (fun _=>rfl)
  let ps := composition (pair xs xs) listProduct
  let good := composition (pair first ps) (filterWith G)
  exact (composition (pair (composition good (TreeTyped.map inl))
    (composition (composition second.snd finsetList) (TreeTyped.map inr))) append).congr (fun _=>rfl)
lemma polynomial_updateList {g : C×(I×I)→Bool} {G : Realizer g} (hG : PolynomialTime G) :
    PolynomialTime (updateListRealizer G) := by
  unfold updateListRealizer
  dsimp only [Realizer.fst, Realizer.snd]
  apply polynomial_congr
  have := polynomial_listProduct (A:=I) (B:=I)
  have := polynomial_filterWithList hG
  have := polynomial_inl (A:=I×I) (B:=I)
  have := polynomial_inr (A:=I×I) (B:=I)
  tree_cost

def updateEqual (E : Realizer (fun x : I×I=>decide (x.1=x.2))) :
    Realizer (fun x : Replica.Update I×Replica.Update I=>@decide (x.1=x.2) (LinearOrder.toDecidableEq x.1 x.2)) :=
  (sumEqual (pairEqual E E) E).congr (by
    intro x; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq])
omit [Codec C] in
lemma polynomial_updateEqual {E : Realizer (fun x : I×I=>decide (x.1=x.2))} (hE : PolynomialTime E) :
    PolynomialTime (updateEqual E) :=
  polynomial_congr _ (polynomial_sumEqual (polynomial_pairEqual hE hE) hE)

def updateSetRealizer {g : C×(I×I)→Bool} (G : Realizer g)
    (E : Realizer (fun x : I×I=>decide (x.1=x.2)))
    (R : Realizer (fun x : I×I=>decide (x.1≤x.2))) :
    Realizer (fun x=> (updateList g x).toFinset) :=
  (composition (updateListRealizer G)
    (listFinset (updateEqual E) (sumLexLe (lexLe E R R) R))).congr (by intro x; ext a; simp)
lemma polynomial_updateSet {g : C×(I×I)→Bool} {G : Realizer g}
    {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    {R : Realizer (fun x : I×I=>decide (x.1≤x.2))}
    (hG : PolynomialTime G) (hE : PolynomialTime E) (hR : PolynomialTime R) :
    PolynomialTime (updateSetRealizer G E R) := by
  unfold updateSetRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_updateList hG)
    (polynomial_listFinset (polynomial_updateEqual hE)
      (polynomial_sumLexLe (polynomial_lexLe hE hR hR) hR))

def scanChoice (g : C×(I×I)→Bool) (x : ScanSetup C I) : Options (Option (Replica.Update I)) :=
  mix ((1,2),(pure none,ExecutableOptions.map (fun x : Bool×Replica.Update I=>Option.some x.2)
    (false,uniform (updateList g x).toFinset)))
def scanChoiceRealizer {g : C×(I×I)→Bool} (G : Realizer g)
    (E : Realizer (fun x : I×I=>decide (x.1=x.2)))
    (R : Realizer (fun x : I×I=>decide (x.1≤x.2))) : Realizer (scanChoice g) :=
  (composition (pair (constant (1,2)) (pair (composition (constant none) pureRealizer)
    (composition (pair (constant false) (composition (updateSetRealizer G E R) uniformRealizer))
      (mapRealizer (composition second TreeTyped.some))))) mixRealizer).congr (fun _=>rfl)
lemma polynomial_scanChoice {g : C×(I×I)→Bool} {G : Realizer g}
    {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    {R : Realizer (fun x : I×I=>decide (x.1≤x.2))}
    (hG : PolynomialTime G) (hE : PolynomialTime E) (hR : PolynomialTime R) :
    PolynomialTime (scanChoiceRealizer G E R) := by
  unfold scanChoiceRealizer
  apply polynomial_congr
  have := polynomial_updateSet hG hE hR
  have := polynomial_uniform (A:=Replica.Update I)
  have := polynomial_pure (A:=Option (Replica.Update I))
  have := polynomial_mix (A:=Option (Replica.Update I))
  have := ExecutableOptions.polynomial_map (polynomial_composition (polynomial_second (A:=Bool) (B:=Replica.Update I)) (polynomial_some (A:=Replica.Update I)))
  tree_cost

variable [Fintype I]
variable (guides : I→Finset I) (base : Finset I) (hb : base.Nonempty)
variable (g : C×(I×I)→Bool) (c : C) (hg : ∀ i j,g (c,(i,j))=decide (j∈guides i))
omit [Codec I] [Codec C] [Inhabited I] in
include hg in
lemma updateSet_eq : (updateList g (c,(Finset.univ,base))).toFinset=Replica.updates guides base := by
  ext u
  cases u with
  | inl ij => rcases ij with ⟨i,j⟩; simp [updateList,Replica.updates,hg]
  | inr i => simp [updateList,Replica.updates]
omit [Codec I] [Codec C] [Inhabited I] in
include hg in
lemma scanChoice_eq : scanChoice g (c,(Finset.univ,base))=
    ExecutableOptions.repr id (Replica.scanChoice guides base hb) := by
  unfold scanChoice Replica.scanChoice
  rw [updateSet_eq guides base g c hg,uniform_repr _ (Replica.updates_nonempty guides base hb)]
  rw [map_repr id id Option.some (fun x : Bool×Replica.Update I=>Option.some x.2) false (fun _=>rfl)]
  have hp := pure_repr (id : Option (Replica.Update I)→_) (none : Option (Replica.Update I))
  dsimp only [id_eq] at hp
  rw [hp]
  have hh : (1,2)=TreeFraction.repr (1/2:ℚ) := by norm_num [TreeFraction.repr]
  rw [hh,mix_repr id (1/2) (by norm_num) (by norm_num)]
end MatchingFPRAS.ExecutableLadder

end OAI
