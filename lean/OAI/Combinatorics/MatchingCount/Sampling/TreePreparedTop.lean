import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreePrepared

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder UnitRefresh Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L} {G : SimpleGraph L}
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)
variable (rank : L→ℕ) (parent : L→Option L)
variable (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
variable (hp : ∀ l p,parent l=some p → rank p<rank l)

lemma preparedTop_source (ft fq : List Bool) (hq : 0<fq.length)
    (w : BagEdge bags→ℚ) (hw : ∀ e,0≤w e) (M : BagPM bags)
    (a : ExecutableDP.Bags) (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags)))
    {k n : ℕ} (bits : Fin n→ScanBits V k) :
    preparedTop (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
      (sourcePrepared rank parent w a ft fq,Numbered.set M.val))=
      Numbered.set (ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) bits
        (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length)))).val := by
  let z : Slot ft.length fq.length := toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length))
  let : Inhabited (Slot ft.length fq.length) := ⟨z⟩
  have hz : index (default : Slot ft.length fq.length)=0 := slot_default_zero _ _ hq
  let keys := List.ofFn (orderedEnum (Slot ft.length fq.length))
  let setup := ((sourceContext (T:=ft.length) (q:=fq.length) rank parent w a,
    ((Finset.univ : Finset (Slot ft.length fq.length)),base ft.length fq.length)),
    (keys,Numbered.set (Finset.univ : Finset (BagEdge bags))))
  let tx : TypedInput (Slot ft.length fq.length) :=
    (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
      (setup,stateRep keys (fun _=>Numbered.set M.val)))
  have hi : (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
      prepareState (sourcePrepared rank parent w a ft fq,Numbered.set M.val))=numericInput tx := by
    refine Prod.ext rfl ?_
    exact prepareState_source ft fq rank parent w hw a M
  unfold preparedTop preparedRun
  dsimp only
  rw [hi,execute_state hz]
  have hr := source_run (T:=ft.length) (q:=fq.length) hbags hG rank parent hb hne hp hq w M a ha
    (fun _=>M) bits
  change typedExecute tx=(setup,stateRep keys (fun i=>Numbered.set
    (ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) bits i).val)) at hr
  rw [hr]
  change lookup ∅ (numericState (stateRep keys (fun i=>Numbered.set
    (ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) bits i).val)),0)=_
  have hz' : index z=0 := hz
  have hmem : z∈keys := by
    simp only [keys,List.mem_ofFn]
    exact ⟨(orderedEnum _).symm z,Equiv.apply_symm_apply _ _⟩
  have hl := lookup_numeric_state keys (fun i=>Numbered.set
    (ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) bits i).val) z hmem
  simpa only [hz'] using hl

theorem source_preparedTop_post : ∃ p : Polynomial ℕ,
    ∀ {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
      {bags : V→Finset L} {G : SimpleGraph L}
      (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)
      (rank : L→ℕ) (parent : L→Option L) (hb : RankedBags bags rank parent)
      (hne : ∀ v,(bags v).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
      (ft fq : List Bool) (hq : 0<fq.length)
      (w : BagEdge bags→ℚ) (_ : ∀ e,0≤w e) (M : BagPM bags)
      (a : ExecutableDP.Bags),List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags)) →
      ∀ {k n : ℕ} (bits : Fin n→ScanBits V k) (t : ℕ),
      let x := (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
        (sourcePrepared rank parent w a ft fq,Numbered.set M.val))
      p.eval (TreePost.packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (TreePost.machine preparedTopRealizer.program) (TreePost.packed x) coins).state=none ∧
      (run (TreePost.machine preparedTopRealizer.program) (TreePost.packed x) coins).tape.right₀=
        Turing.ListBlank.mk (TreePost.packed (Numbered.set
          (ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) bits
            (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length)))).val)) := by
  obtain ⟨p,hp⟩:=preparedTop_post
  refine ⟨p,fun {V L} _ _ _ _ {bags G} hbags hG rank parent hb hne hparent ft fq hq w hw M a ha {k n} bits t ht coins=>?_⟩
  have h:=hp (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
    (sourcePrepared rank parent w a ft fq,Numbered.set M.val)) t ht coins
  rwa [preparedTop_source hbags hG rank parent hb hne hparent ft fq hq w hw M a ha bits] at h
end MatchingFPRAS.NumericLadder

end OAI
