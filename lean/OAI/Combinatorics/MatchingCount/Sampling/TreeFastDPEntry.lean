import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreePolyTactic
import OAI.Combinatorics.MatchingCount.Machines.TreeFastLookup
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialSums
import OAI.Combinatorics.MatchingCount.Machines.TreeFastChoose

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Polynomial

def readFast : Realizer read :=
  composition (pair (composition (pair first second.fst) (getDFast [])) second.snd) (getDFast 0)
lemma polynomial_readFast : PolynomialTime readFast := by
  unfold readFast
  dsimp only [Realizer.fst, Realizer.snd]
  apply polynomial_composition _ (polynomial_getDFast 0)
  apply polynomial_pair _ (polynomial_snd polynomial_second)
  apply polynomial_composition _ (polynomial_getDFast [])
  tree_poly

lemma polynomial_totalFlag : PolynomialTime totalFlagRealizer := by
  unfold totalFlagRealizer
  apply polynomial_composition _ polynomial_membership
  tree_poly
lemma polynomial_countWith {A B : Type} [Codec A] [Codec B] {p : A×B → Bool}
    {P : Realizer p} (hP : PolynomialTime P) : PolynomialTime (countWith P) := by
  unfold countWith countTrue
  exact polynomial_congr _ (polynomial_composition (polynomial_mapWith hP)
    (polynomial_composition (polynomial_filter polynomial_identity) polynomial_listLength))

lemma polynomial_privateFlag : PolynomialTime privateFlagRealizer := by
  unfold privateFlagRealizer
  apply polynomial_composition _ polynomial_boolAnd
  apply polynomial_pair _ polynomial_totalFlag
  tree_poly
lemma polynomial_sharedFlag : PolynomialTime sharedFlagRealizer := by
  unfold sharedFlagRealizer
  exact polynomial_composition (polynomial_pair polynomial_totalFlag
    (polynomial_composition polynomial_privateFlag polynomial_boolNot)) polynomial_boolAnd
lemma polynomial_privateNumber : PolynomialTime privateNumberRealizer := by
  unfold privateNumberRealizer
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_countWith polynomial_privateFlag)
  tree_poly
lemma polynomial_sharedNumber : PolynomialTime sharedNumberRealizer := by
  unfold sharedNumberRealizer
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_countWith polynomial_sharedFlag)
  tree_poly
lemma polynomial_totalNumber : PolynomialTime totalNumberRealizer := by
  unfold totalNumberRealizer
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_countWith polynomial_totalFlag)
  tree_poly
lemma polynomial_trim : PolynomialTime trimRealizer := by
  unfold trimRealizer
  apply polynomial_composition _ (polynomial_filterWith (polynomial_composition polynomial_totalFlag polynomial_boolNot))
  tree_poly

abbrev RawCtx := (Bags×Parents)×(ℕ×Table)
def contextFast : Realizer context := by
  let bl : Realizer (fun x : RawCtx=>(x.1.1,x.2.1)) := pair first.fst second.fst
  let p := composition bl privateNumberRealizer
  let q := composition bl sharedNumberRealizer
  let r := composition bl totalNumberRealizer
  exact (pair (composition (pair first.snd second.fst) (getDFast (false,0)))
    (pair second.fst (pair second.snd (pair p (pair q r))))).congr (fun _=>rfl)
lemma polynomial_contextFast : PolynomialTime contextFast := by
  unfold contextFast
  dsimp only [Realizer.fst, Realizer.snd]
  apply polynomial_congr
  apply polynomial_pair
  · apply polynomial_composition _ (polynomial_getDFast (false,0))
    tree_poly
  · apply polynomial_pair (polynomial_fst polynomial_second)
    apply polynomial_pair (polynomial_snd polynomial_second)
    apply polynomial_pair
    · apply polynomial_composition _ polynomial_privateNumber
      tree_poly
    · apply polynomial_pair
      · apply polynomial_composition _ polynomial_sharedNumber
        tree_poly
      · apply polynomial_composition _ polynomial_totalNumber
        tree_poly

def rawTerm (x : (RawCtx×ℕ)×ℕ) : ℕ := term ((context x.1.1,x.1.2),x.2)
def rawTermRealizer : Realizer rawTerm := by
  let raw : Realizer (fun x : (RawCtx×ℕ)×ℕ=>x.1.1) := first.fst
  let c := composition raw contextFast
  let r : Realizer (fun x : (RawCtx×ℕ)×ℕ=>x.1.2) := first.snd
  let k : Realizer (fun x : (RawCtx×ℕ)×ℕ=>x.2) := second
  let s := c.snd.snd.snd.snd.fst
  let u := c.snd.snd.snd.fst
  let t := c.snd.snd.fst
  let l := c.snd.fst
  let p := c.fst.snd
  let ch := composition (pair s k) fastChoose
  let L := composition (pair t (pair l (composition (pair u k) add))) readFast
  let R := composition (pair t (pair p (composition (pair (composition (pair s k) subtract) r) add))) readFast
  exact (composition (pair (composition (pair ch L) multiply) R) multiply).congr (fun _=>rfl)
lemma sharedNumber_le (bs : Bags) (l : ℕ) : sharedNumber bs l≤bs.length := List.length_filter_le _ _
lemma polynomial_rawTerm : PolynomialTime rawTermRealizer := by
  unfold rawTermRealizer
  dsimp only [Realizer.fst, Realizer.snd]
  apply polynomial_congr
  have hc:=polynomial_contextFast
  have hr:=polynomial_readFast
  have hch : PolynomialTime (composition
      (pair (composition first.fst contextFast).snd.snd.snd.snd.fst (second (A:=RawCtx×ℕ) (B:=ℕ))) fastChoose) := by
    apply polynomial_boundedFastChoose (by dsimp only [Realizer.fst, Realizer.snd]; tree_poly) X
    intro x
    simp only [Polynomial.eval_X]
    change sharedNumber x.1.1.1.1 x.1.1.2.1≤weight x
    exact (sharedNumber_le _ _).trans ((list_length_le_weight _).trans (by
      rcases x with ⟨⟨⟨⟨bs,ps⟩,⟨l,t⟩⟩,r⟩,k⟩
      simp only [weight_prod]; omega))
  dsimp only [Realizer.fst, Realizer.snd] at hch
  tree_poly

def rawEntry (x : RawCtx×(ℕ×ℕ)) : ℕ := entry (context x.1,x.2)
def rawEntryRealizer : Realizer rawEntry := by
  let raw : Realizer (fun x : RawCtx×(ℕ×ℕ)=>x.1) := first
  let c := composition raw contextFast
  let a : Realizer (fun x : RawCtx×(ℕ×ℕ)=>x.2.1) := second.fst
  let r : Realizer (fun x : RawCtx×(ℕ×ℕ)=>x.2.2) := second.snd
  let l := c.snd.fst
  let rd := composition (pair c.snd.snd.fst (pair a r)) readFast
  let al := composition (pair a l) natEqual
  let ap := composition (pair a c.fst.snd) natEqual
  let ks := composition (composition c.snd.snd.snd.snd.fst successor) range
  let sm := composition (composition (pair (pair raw r) ks) (mapWith rawTermRealizer)) listSum
  let rt := composition (pair c.snd.snd.fst (pair l c.snd.snd.snd.snd.snd)) readFast
  exact (choose c.fst.fst (choose al (constant 1) (choose ap sm rd)) (choose al rt rd)).congr (by
    intro x; simp only [rawEntry,entry,rawTerm,Function.comp_apply,decide_eq_true_eq])
lemma polynomial_rawEntry : PolynomialTime rawEntryRealizer := by
  unfold rawEntryRealizer
  dsimp only [Realizer.fst, Realizer.snd]
  have hc:=polynomial_contextFast
  have hr:=polynomial_readFast
  have ht:=polynomial_rawTerm
  have hs:=polynomial_listSum
  have hks : PolynomialTime (composition (composition
      (composition (first (A:=RawCtx) (B:=ℕ×ℕ)) contextFast).snd.snd.snd.snd.fst successor) range) := by
    apply polynomial_boundedRange (by
      have := polynomial_successor
      dsimp only [Realizer.fst, Realizer.snd]
      tree_poly) (X+1)
    intro x
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    change sharedNumber x.1.1.1 x.1.2.1+1≤weight x+1
    have hh:=sharedNumber_le x.1.1.1 x.1.2.1
    have hw:=list_length_le_weight x.1.1.1
    rcases x with ⟨⟨⟨bs,ps⟩,⟨l,t⟩⟩,ar⟩
    simp only [weight_prod]
    dsimp only at hh hw
    omega
  dsimp only [Realizer.fst, Realizer.snd] at hks
  tree_poly
end MatchingFPRAS.ExecutableDP

end OAI
