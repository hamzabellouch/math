import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostTactic

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B]

def listProduct : Realizer (fun x : List A×List B=>x.1.product x.2) :=
  (composition (composition (pair second first)
    (mapWith (composition (pair second first) (mapWith (pair first second))))) flatten).congr (fun _=>rfl)
lemma polynomial_listProduct : PolynomialTime (listProduct (A:=A) (B:=B)) := by
  unfold listProduct
  apply polynomial_congr
  tree_cost

omit [Codec A] [Codec B] in
lemma mem_listProduct (a : A) (b : B) (s : List A) (t : List B) :
    (a,b)∈s.product t ↔ a∈s ∧ b∈t := List.mem_product

abbrev Quad (A : Type) := (A×A)×(A×A)
def quadList (q : Quad A) : List A := [q.1.1,q.1.2,q.2.1,q.2.2]
def quadFn (q : Quad A) : Fin 4→A := ![q.1.1,q.1.2,q.2.1,q.2.2]
def quadOfFn (f : Fin 4→A) : Quad A := ((f 0,f 1),(f 2,f 3))
omit [Codec A] [Codec B] in
lemma quadFn_ofFn (f : Fin 4→A) : quadFn (quadOfFn f)=f := by
  funext i
  fin_cases i <;> rfl
omit [Codec A] [Codec B] in
lemma quadList_ofFn (q : Quad A) : quadList q=List.ofFn (quadFn q) := by
  simp [quadList,quadFn,List.ofFn_succ]
def quadListRealizer : Realizer (quadList (A:=A)) :=
  (composition (pair first.fst (composition (pair first.snd
    (composition (pair second.fst (composition (pair second.snd (constant ([] : List A))) listCons)) listCons)) listCons)) listCons).congr (fun _=>rfl)
lemma polynomial_quadList : PolynomialTime (quadListRealizer (A:=A)) := by
  unfold quadListRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  tree_cost

def quads (s : List A) : List (Quad A) := (s.product s).product (s.product s)
def quadsRealizer : Realizer (quads (A:=A)) :=
  (composition (pair (composition (pair identity identity) listProduct)
    (composition (pair identity identity) listProduct)) listProduct).congr (fun _=>rfl)
lemma polynomial_quads : PolynomialTime (quadsRealizer (A:=A)) := by
  unfold quadsRealizer
  apply polynomial_congr
  have := polynomial_listProduct (A:=A) (B:=A)
  have := polynomial_listProduct (A:=A×A) (B:=A×A)
  tree_cost
omit [Codec A] [Codec B] in
lemma mem_quads (q : Quad A) (s : List A) : q∈quads s ↔ ∀ i,quadFn q i∈s := by
  rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp only [quads,mem_listProduct]
  constructor
  · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩
end MatchingFPRAS.TreeTyped

end OAI
