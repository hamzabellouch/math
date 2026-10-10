import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeSum

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B A' B' : Type} [Codec A] [Codec B] [Codec A'] [Codec B']
def Realizer.reencode {f : A→B} (F : Realizer f) (i : A'→A) (g : A'→B')
    (hi : ∀ a,encode (i a)=encode a) (hg : ∀ a,encode (g a)=encode (f (i a))) : Realizer g where
  program := F.program
  cost a := F.cost (i a)
  correct := by
    intro a s
    have h:=F.correct (i a) s
    rw [hi a,←hg a] at h
    exact h
lemma polynomial_reencode {f : A→B} (F : Realizer f) (i : A'→A) (g : A'→B')
    (hi : ∀ a,encode (i a)=encode a) (hg : ∀ a,encode (g a)=encode (f (i a)))
    (hF : PolynomialTime F) : PolynomialTime (F.reencode i g hi hg) := by
  obtain ⟨p,hp⟩:=hF
  refine ⟨p,fun a=>?_⟩
  have h:=hp (i a)
  simpa only [Realizer.reencode,weight,hi a,←hg a] using h
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.LiteralCodec
open TreeTyped TreeData TreeFunction

def parts (a : Symbol) : List Bool×List Bool :=
  (List.replicate a.val false,List.replicate (7-a.val) false)
instance : Codec Symbol := ⟨fun a=>TreeTyped.encode (parts a)⟩
lemma encode_parts (a : Symbol) : TreeTyped.encode (parts a)=TreeTyped.encode a := rfl
lemma weight_false_list (n : ℕ) : weight (List.replicate n false)=2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,weight_cons,ih]; change 1+1+(2*n+1)=_; omega
lemma weight_symbol (a : Symbol) : weight a=17 := by
  change weight (parts a)=17
  simp only [parts,weight_prod,weight_false_list]
  have ha:=a.isLt
  omega
lemma weight_word (as : List Symbol) : weight as=18*as.length+1 := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [weight_cons,weight_symbol,ih,List.length_cons]; omega

def valRealizer : Realizer (Fin.val : Symbol→ℕ) :=
  (composition first listLength).reencode parts Fin.val encode_parts (fun a=>by simp [parts])
lemma polynomial_val : PolynomialTime valRealizer :=
  polynomial_reencode _ _ _ _ _ (polynomial_composition polynomial_first polynomial_listLength)

def fromBit (b : Bool) : Symbol := if b then 2 else 1
def fromBitRealizer : Realizer fromBit := choose identity (constant 2) (constant 1)
lemma polynomial_fromBit : PolynomialTime fromBitRealizer :=
  polynomial_choose polynomial_identity (polynomial_constant _) (polynomial_constant _)
def natWord (n : ℕ) : List Symbol := (n.bits.map fromBit)++[3]
def natWordRealizer : Realizer natWord :=
  (composition (pair (composition toBits (map fromBitRealizer)) (constant [3])) append).congr (fun _=>rfl)
lemma polynomial_natWord : PolynomialTime natWordRealizer := by
  unfold natWordRealizer
  apply polynomial_congr
  have := polynomial_fromBit
  have := polynomial_toBits
  have := polynomial_map polynomial_fromBit
  tree_cost
lemma natWord_eq (n : ℕ) : natWord n=encodeNat n := rfl

def ratWord (x : TreeFraction.Fraction) : List Symbol := 4::natWord x.1++natWord x.2
def ratWordRealizer : Realizer ratWord :=
  (composition (pair (constant 4) (composition (pair (composition first natWordRealizer)
    (composition second natWordRealizer)) append)) listCons).congr (fun _=>rfl)
lemma polynomial_ratWord : PolynomialTime ratWordRealizer := by
  unfold ratWordRealizer
  apply polynomial_congr
  have := polynomial_natWord
  tree_cost
lemma ratWord_repr (q : ℚ) (hq : 0≤q) : ratWord (TreeFraction.repr q)=encodeRat q := by
  have hn : ¬q.num<0 := not_lt.mpr (Rat.num_nonneg.mpr hq)
  simp only [ratWord,TreeFraction.repr,natWord_eq,encodeRat,encodeInt,ite_eq_right hn,List.singleton_append]
end MatchingFPRAS.LiteralCodec

end OAI
