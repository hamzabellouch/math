import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.TreeMatchingCheck

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

def certify (p : C×(E×V)→Bool) (x : (C×Finset V)×Finset (Finset E)) : Finset (Finset E) :=
  x.2.filter (fun a=>matchingCheck p (x.1,a)=true)
def certifyRealizer {p : C×(E×V)→Bool} (P : Realizer p) : Realizer (certify p) :=
  (finsetFilterWith (matchingCheckRealizer P)).congr (fun _=>rfl)
lemma polynomial_certify {p : C×(E×V)→Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (certifyRealizer P) :=
  polynomial_congr _ (polynomial_finsetFilterWith (polynomial_matchingCheck hP))

variable [Fintype E] [Fintype V] (ends : E→Sym2 V)
attribute [local instance] Transport.Sparse.pmOrder

def pmEmbedding : @OrderEmbedding (Transport.PM (fun e v=>v∈ends e)) (Finset E)
    (Transport.Sparse.pmOrder ends).toLE (Transport.Sparse.finsetOrder (E:=E)).toLE :=
  { toFun := Subtype.val
    inj' := Subtype.val_injective
    map_rel_iff' := Iff.rfl }

omit [Codec E] [Codec V] [Codec C] in
lemma certify_eq (p : C×(E×V)→Bool) (c : C)
    (hp : ∀ e v,p (c,(e,v))=decide (v∈ends e)) (s : Finset (Finset E)) :
    certify p ((c,Finset.univ),s)=(Transport.Sparse.certify ends s).map (pmEmbedding ends).toEmbedding := by
  ext a
  simp only [certify,Finset.mem_filter,matchingCheck_eq p c _ hp,decide_eq_true_eq,
    Finset.mem_map,pmEmbedding]
  constructor
  · rintro ⟨ha,hm⟩
    exact ⟨⟨a,hm⟩,by simpa using ha,rfl⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨by simpa using hb,b.property⟩
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
