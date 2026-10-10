import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeNumericLadder
import OAI.Combinatorics.MatchingCount.Sampling.TreeIndexedPairResult

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered UnitRefresh ExecutablePair

variable {I E V : Type} [Fintype I] [LinearOrder I] [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
def contextRep (ends : E→Sym2 V) (w : I→E→ℚ) (guides : I→Finset I) (refresh : RefreshSetup) : Context :=
  let eps := List.ofFn (fun e=>endpointRep (ends (orderedEnum E e)))
  let rows := List.ofFn (fun i=>List.ofFn (fun e=>TreeFraction.repr (w (orderedEnum I i) (orderedEnum E e))))
  let univ := (Numbered.set (Finset.univ : Finset V),Numbered.set (Finset.univ : Finset E))
  let gs := List.ofFn (fun i=>(Numbered.set (guides (orderedEnum I i))).sort (·≤·))
  ((((eps,rows),univ),refresh),gs)
lemma row_rep (ends : E→Sym2 V) (w : I→E→ℚ) (guides : I→Finset I) (refresh : RefreshSetup) (i : I) :
    row (contextRep ends w guides refresh,index i)=List.ofFn (fun e=>TreeFraction.repr (w i (orderedEnum E e))) := by
  simp [row,contextRep,index,List.getD_eq_getElem?_getD]
lemma guides_rep (ends : E→Sym2 V) (w : I→E→ℚ) (guides : I→Finset I) (refresh : RefreshSetup) (i j : I) :
    guide (contextRep ends w guides refresh,(index i,index j))=decide (j∈guides i) := by
  simp [guide,contextRep,index,List.getD_eq_getElem?_getD,Numbered.set,Numbered.embedding,Numbered.index]
  constructor
  · rintro ⟨a,ha,h⟩
    have he : a=j := (orderedEnum I).symm.injective (Fin.ext h)
    simpa [he] using ha
  · intro hj; exact ⟨j,hj,rfl⟩
lemma pairContext_rep (ends : E→Sym2 V) (w : I→E→ℚ) (guides : I→Finset I) (refresh : RefreshSetup) (i j : I) :
    pairContext (contextRep ends w guides refresh,(index i,index j))=ExecutablePair.contextRep ends (w i) (w j) := by
  simp only [pairContext,row_rep]
  rfl
attribute [local instance] Transport.Sparse.pmOrder
lemma pairDraw_rep (ends : E→Sym2 V) (hloop : ∀ e,¬(ends e).IsDiag)
    (hpar : ∀ e,(Finset.univ.filter (fun f=>ends f=ends e)).card≤2)
    (w : I→E→ℚ) (hw : ∀ i e,0<w i e) (guides : I→Finset I) (refresh : RefreshSetup)
    (i j : I) (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e))
    {k : ℕ} (bits : Fin k→Bool) (other : ExecutableUnit.Bits) :
    pairDraw ((contextRep ends w guides refresh,(index i,index j)),
      ((Numbered.set a.1.val,Numbered.set a.2.val),(List.ofFn bits,other)))=
    (Numbered.set ((Transport.Sparse.pairStepTable ends hloop hpar (w i) (w j) (hw i) (hw j) a).draw k bits).1.val,
     Numbered.set ((Transport.Sparse.pairStepTable ends hloop hpar (w i) (w j) (hw i) (hw j) a).draw k bits).2.val) := by
  unfold pairDraw
  rw [pairContext_rep]
  exact numeric_draw_source ends hloop hpar (w i) (w j) (hw i) (hw j) a bits
end MatchingFPRAS.NumericLadder

end OAI
