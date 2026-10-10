import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeLadder
import OAI.Combinatorics.MatchingCount.Sampling.TreePrepareLadder
import OAI.Combinatorics.MatchingCount.Algorithm.TreeReweight

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder UnitRefresh Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma execute_state {I : Type} [Fintype I] [LinearOrder I] [Inhabited I]
    (hz : index (default : I)=0) (x : TypedInput I) :
    (execute (numericInput x)).2=numericState (typedExecute x).2 := by
  apply list_encode_injective (pair_encode_injective nat_encode_injective finsetNat_encode_injective)
  have h:=TreePost.sameProgram_encode executeRealizer typedExecuteRealizer (typedExecute_program hz).symm
    _ _ (numericInput_encode x)
  exact (TreeData.Data.cons.inj h).2.trans (numericState_encode _).symm

variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}
def sourcePrepared (rank : L→ℕ) (parent : L→Option L) (w : BagEdge bags→ℚ)
    (a : ExecutableDP.Bags) (ft fq : List Bool) : Prepared :=
  ((((Fintype.card V,ft),(fq,List.ofFn (fun e=>TreeFraction.repr (w (orderedEnum _ e))))),
    (List.ofFn (fun e=>ExecutablePair.endpointRep (orderedEnum (BagEdge bags) e).val.val.1),
      (Numbered.set (Finset.univ : Finset V),Numbered.set (Finset.univ : Finset (BagEdge bags))))),
    (ExecutableRefresh.storedCatalog (a,List.range (Fintype.card L)),
      ((a,ExecutableDP.parentRep (numberedParent parent)),(Materialized.plan (numberedRank rank)).map Fin.val)))

lemma prepareContext_source (rank : L→ℕ) (parent : L→Option L) (w : BagEdge bags→ℚ)
    (hw : ∀ e,0≤w e) (a : ExecutableDP.Bags) (ft fq : List Bool) :
    prepareContext (sourcePrepared rank parent w a ft fq)=
      sourceContext (T:=ft.length) (q:=fq.length) rank parent w a := by
  unfold prepareContext sourcePrepared
  dsimp only
  rw [weightRows_source w hw ft fq,guideRows_source]
  rfl

lemma slots_source (n : ℕ) (ft fq : List Bool) (ws : List Fraction) :
    slots ((n,ft),(fq,ws))=(List.ofFn (orderedEnum (Slot ft.length fq.length))).map index := by
  rw [List.map_ofFn]
  exact range_slot_indices ft.length fq.length

lemma prepareSetup_source
    (rank : L→ℕ) (parent : L→Option L) (w : BagEdge bags→ℚ)
    (hw : ∀ e,0≤w e) (a : ExecutableDP.Bags) (ft fq : List Bool) :
    prepareSetup (sourcePrepared rank parent w a ft fq)=numericSetup
      ((sourceContext (T:=ft.length) (q:=fq.length) rank parent w a,(Finset.univ,base ft.length fq.length)),
        (List.ofFn (orderedEnum (Slot ft.length fq.length)),Numbered.set (Finset.univ : Finset (BagEdge bags)))) := by
  unfold prepareSetup
  rw [prepareContext_source rank parent w hw a ft fq]
  dsimp only [sourcePrepared]
  rw [slotUniverse_source,baseSet_source,slots_source]
  rfl

lemma prepareState_source (ft fq : List Bool) [Inhabited (Slot ft.length fq.length)]
    (rank : L→ℕ) (parent : L→Option L) (w : BagEdge bags→ℚ)
    (hw : ∀ e,0≤w e) (a : ExecutableDP.Bags) (M : BagPM bags) :
    prepareState (sourcePrepared rank parent w a ft fq,Numbered.set M.val)=
      (numericSetup ((sourceContext (T:=ft.length) (q:=fq.length) rank parent w a,(Finset.univ,base ft.length fq.length)),
        (List.ofFn (orderedEnum (Slot ft.length fq.length)),Numbered.set (Finset.univ : Finset (BagEdge bags)))),
       numericState (stateRep (List.ofFn (orderedEnum (Slot ft.length fq.length))) (fun _=>Numbered.set M.val))) := by
  unfold prepareState
  dsimp only
  rw [prepareSetup_source rank parent w hw a ft fq]
  refine Prod.ext rfl ?_
  dsimp only [sourcePrepared]
  rw [slots_source]
  simp only [numericState,stateRep,List.map_map,Function.comp_def]

lemma lookup_numeric_state {I : Type} [Fintype I] [LinearOrder I] [Inhabited I]
    (keys : List I) (f : I→Finset ℕ) (i : I) (hi : i∈keys) :
    lookup ∅ (numericState (stateRep keys f),index i)=f i := by
  simp only [numericState,stateRep,List.map_map,Function.comp_def]
  exact lookup_image ∅ keys index f index_injective i hi
end MatchingFPRAS.NumericLadder

end OAI
