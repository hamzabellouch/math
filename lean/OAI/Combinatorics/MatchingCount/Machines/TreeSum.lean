import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostTactic

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

def sumRep [Inhabited A] [Inhabited B] : A⊕B→Bool×(A×B)
  | .inl a => (true,(a,default))
  | .inr b => (false,(default,b))
instance [Inhabited A] [Inhabited B] : Codec (A⊕B) := ⟨fun x=>encode (sumRep x)⟩

def inl [Inhabited A] [Inhabited B] : Realizer (Sum.inl : A→A⊕B) :=
  (pair (constant true) (pair identity (constant (default : B)))).recode id Sum.inl (fun _=>rfl) (fun _=>rfl)
def inr [Inhabited A] [Inhabited B] : Realizer (Sum.inr : B→A⊕B) :=
  (pair (constant false) (pair (constant (default : A)) identity)).recode id Sum.inr (fun _=>rfl) (fun _=>rfl)
omit [Codec C] [Codec D] in
lemma polynomial_inl [Inhabited A] [Inhabited B] : PolynomialTime (inl (A:=A) (B:=B)) := by
  unfold inl
  apply polynomial_recode
  tree_cost
omit [Codec C] [Codec D] in
lemma polynomial_inr [Inhabited A] [Inhabited B] : PolynomialTime (inr (A:=A) (B:=B)) := by
  unfold inr
  apply polynomial_recode
  tree_cost

def sumCases [Inhabited A] [Inhabited B] {f : C×A→D} {g : C×B→D}
    (F : Realizer f) (G : Realizer g) : Realizer (fun x : C×(A⊕B)=>Sum.elim (fun a=>f (x.1,a)) (fun b=>g (x.1,b)) x.2) :=
  (choose second.fst (composition (pair first second.snd.fst) F)
    (composition (pair first second.snd.snd) G)).recode
      (fun x : C×(A⊕B)=>(x.1,sumRep x.2))
      (fun x=>Sum.elim (fun a=>f (x.1,a)) (fun b=>g (x.1,b)) x.2)
      (fun _=>rfl) (by intro x; cases x.2 <;> rfl)
lemma polynomial_sumCases [Inhabited A] [Inhabited B] {f : C×A→D} {g : C×B→D}
    {F : Realizer f} {G : Realizer g} (hF : PolynomialTime F) (hG : PolynomialTime G) :
    PolynomialTime (sumCases F G) := by
  unfold sumCases
  apply polynomial_recode
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def sumEqual [Inhabited A] [Inhabited B] [DecidableEq A] [DecidableEq B]
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (F : Realizer (fun x : B×B=>decide (x.1=x.2))) :
    Realizer (fun x : (A⊕B)×(A⊕B)=>decide (x.1=x.2)) :=
  (sumCases (composition (pair second first) (sumCases E (constant false)))
    (composition (pair second first) (sumCases (constant false) F))).congr (by
      intro x; rcases x with ⟨x,y⟩; cases x <;> cases y <;> simp [eq_comm])
omit [Codec C] [Codec D] in
lemma polynomial_sumEqual [Inhabited A] [Inhabited B] [DecidableEq A] [DecidableEq B]
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {F : Realizer (fun x : B×B=>decide (x.1=x.2))}
    (hE : PolynomialTime E) (hF : PolynomialTime F) : PolynomialTime (sumEqual E F) := by
  unfold sumEqual
  apply polynomial_congr
  apply polynomial_sumCases
  · exact polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_sumCases hE (polynomial_constant false))
  · exact polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_sumCases (polynomial_constant false) hF)

def sumLexLe [Inhabited A] [Inhabited B] [LinearOrder A] [LinearOrder B]
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2)))
    (S : Realizer (fun x : B×B=>decide (x.1≤x.2))) :
    Realizer (fun x : (A⊕B)×(A⊕B)=>decide (toLex x.1≤toLex x.2)) :=
  (sumCases (composition (pair second first) (sumCases (composition (pair second first) R) (constant false)))
    (composition (pair second first) (sumCases (constant true) (composition (pair second first) S)))).congr (by
      intro x; rcases x with ⟨x,y⟩; cases x <;> cases y <;> simp)
omit [Codec C] [Codec D] in
lemma polynomial_sumLexLe [Inhabited A] [Inhabited B] [LinearOrder A] [LinearOrder B]
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    {S : Realizer (fun x : B×B=>decide (x.1≤x.2))}
    (hR : PolynomialTime R) (hS : PolynomialTime S) : PolynomialTime (sumLexLe R S) := by
  unfold sumLexLe
  apply polynomial_congr
  apply polynomial_sumCases
  · exact polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_sumCases (polynomial_composition (polynomial_pair polynomial_second polynomial_first) hR)
        (polynomial_constant false))
  · exact polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_sumCases (polynomial_constant true)
        (polynomial_composition (polynomial_pair polynomial_second polynomial_first) hS))

def optionRep [Inhabited A] : Option A→Bool×A
  | none => (false,default)
  | some a => (true,a)
instance [Inhabited A] : Codec (Option A) := ⟨fun x=>encode (optionRep x)⟩
def some [Inhabited A] : Realizer (Option.some : A→Option A) :=
  (pair (constant true) identity).recode id Option.some (fun _=>rfl) (fun _=>rfl)
omit [Codec B] [Codec C] [Codec D] in
lemma polynomial_some [Inhabited A] : PolynomialTime (some (A:=A)) := by
  unfold some
  apply polynomial_recode
  tree_cost

def optionCases [Inhabited A] {f : C→D} {g : C×A→D} (F : Realizer f) (G : Realizer g) :
    Realizer (fun x : C×Option A=>x.2.elim (f x.1) (fun a=>g (x.1,a))) :=
  (choose second.fst (composition (pair first second.snd) G) (composition first F)).recode
    (fun x : C×Option A=>(x.1,optionRep x.2))
    (fun x=>x.2.elim (f x.1) (fun a=>g (x.1,a))) (fun _=>rfl) (by intro x; cases x.2 <;> rfl)
omit [Codec B] in
lemma polynomial_optionCases [Inhabited A] {f : C→D} {g : C×A→D}
    {F : Realizer f} {G : Realizer g} (hF : PolynomialTime F) (hG : PolynomialTime G) :
    PolynomialTime (optionCases F G) := by
  unfold optionCases
  apply polynomial_recode
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost
end MatchingFPRAS.TreeTyped

end OAI
