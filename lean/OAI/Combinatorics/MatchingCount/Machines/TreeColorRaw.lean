import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TreeSparseComponents
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostTactic

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E C : Type} [Codec E] [Codec C] [LinearOrder E]
attribute [local instance] Transport.Sparse.finsetOrder

def colorRaw (p : C×(E×E)→Bool) (x : (C×Finset E)×Finset E) : Finset (Finset E) :=
  x.2.biUnion fun e=>(x.1.2.filter (fun f=>p (x.1.1,(f,e))=true)).image fun f=>insert f (x.2.erase e)
def colorRawRealizer {p : C×(E×E)→Bool} (P : Realizer p)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (colorRaw p) := by
  let choices : Realizer (fun x : ((C×Finset E)×Finset E)×E=>
      x.1.1.2.filter (fun f=>p (x.1.1.1,(f,x.2))=true)) :=
    (composition (pair (pair first.fst.fst second) first.fst.snd)
      (finsetFilterWith (composition (pair first.fst (pair second first.snd)) P))).congr (fun _=>rfl)
  let edit : Realizer (fun x : (((C×Finset E)×Finset E)×E)×E=>
      insert x.2 (x.1.1.2.erase x.1.2)) :=
    (composition (pair second (composition (pair first.snd first.fst.snd) (finsetErase Eq))) (finsetInsert Eq Le)).congr (fun _=>rfl)
  let neighbors : Realizer (fun x : ((C×Finset E)×Finset E)×E=>
      (x.1.1.2.filter (fun f=>p (x.1.1.1,(f,x.2))=true)).image fun f=>insert f (x.1.2.erase x.2)) :=
    (composition (pair identity choices) (finsetImageWith edit (orderedSetEqual Eq) (colexLe Eq Le))).congr (by
      intro x; ext a; simp only [Function.comp_apply,id_eq,Finset.mem_image])
  exact (composition (pair identity second)
    (finsetBiUnion neighbors (orderedSetEqual Eq) (colexLe Eq Le))).congr (by
      intro x; ext a; simp only [Function.comp_apply,id_eq,colorRaw,Finset.mem_biUnion,Finset.mem_image])
lemma polynomial_colorRaw {p : C×(E×E)→Bool} {P : Realizer p}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {Le : Realizer (fun x : E×E=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hEq : PolynomialTime Eq) (hLe : PolynomialTime Le) :
    PolynomialTime (colorRawRealizer P Eq Le) := by
  unfold colorRawRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  have := polynomial_orderedSetEqual hEq
  have := polynomial_colexLe hEq hLe
  apply polynomial_congr
  tree_cost
  all_goals apply polynomial_finsetImageWith <;> tree_cost

omit [Codec E] [Codec C] in
lemma colorRaw_eq [Codec E] [Codec C] [Fintype E] {V : Type} [DecidableEq V] (ends : E→Sym2 V)
    (p : C×(E×E)→Bool) (c : C) (hp : ∀ e f,p (c,(e,f))=decide (ends e=ends f)) (M : Finset E) :
    colorRaw p ((c,Finset.univ),M)=Transport.Sparse.colorRaw ends M := by
  simp only [colorRaw,Transport.Sparse.colorRaw,hp,decide_eq_true_eq]
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
