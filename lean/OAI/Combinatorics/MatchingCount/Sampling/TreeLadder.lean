import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeRefresh
import OAI.Combinatorics.MatchingCount.Sampling.TreeLadderContext
import OAI.Combinatorics.MatchingCount.Sampling.TreeLadderPost

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered ExecutableLadder UnitRefresh Transport Replica.Ladder

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L} {G : SimpleGraph L}
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)
variable (rank : L→ℕ) (parent : L→Option L)
variable (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
variable (hp : ∀ l p,parent l=some p → rank p<rank l)
variable {T q : ℕ} [Inhabited (Slot T q)]

def sourceContext (w : BagEdge bags→ℚ) (a : ExecutableDP.Bags) : Context :=
  contextRep (fun e : BagEdge bags=>e.val.val.1) (rationalSlotWeight (T:=T) (q:=q) w) guides
    (ExecutableRefresh.storedCatalog (a,List.range (Fintype.card L)),
      ((a,ExecutableDP.parentRep (numberedParent parent)),(Materialized.plan (numberedRank rank)).map Fin.val))

def localBitsRep {k : ℕ} (b : LocalBits V k) : Bits :=
  (List.ofFn b.1,List.ofFn (fun i=>List.ofFn (b.2 i)))
omit [Inhabited (Slot T q)] in
lemma source_guide (w : BagEdge bags→ℚ) (a : ExecutableDP.Bags) (i j : Slot T q) :
    typedGuide (sourceContext (T:=T) (q:=q) rank parent w a,(i,j))=decide (j∈guides i) :=
  guides_rep (fun e : BagEdge bags=>e.val.val.1) (rationalSlotWeight (T:=T) (q:=q) w) guides
    (ExecutableRefresh.storedCatalog (a,List.range (Fintype.card L)),
      ((a,ExecutableDP.parentRep (numberedParent parent)),(Materialized.plan (numberedRank rank)).map Fin.val)) i j
omit [Inhabited (Slot T q)] in
lemma source_pair (w : BagEdge bags→ℚ) (a : ExecutableDP.Bags) (i j : Slot T q)
    (s : BagPM bags×BagPM bags) {k : ℕ} (bits : LocalBits V k) :
    typedPair ((sourceContext (T:=T) (q:=q) rank parent w a,(i,j)),
      ((Numbered.set s.1.val,Numbered.set s.2.val),localBitsRep bits))=
      (Numbered.set (Transport.pairDraw hbags hG w k i j s bits).1.val,
       Numbered.set (Transport.pairDraw hbags hG w k i j s bits).2.val) := by
  exact pairDraw_rep (fun e : BagEdge bags=>e.val.val.1) (fun e=>e.val.property)
    (parallels_bound hbags hG) (rationalSlotWeight w) (rationalSlotWeight_pos w) guides _ i j s bits.1 _
omit [Inhabited (Slot T q)] in
lemma source_refresh (w : BagEdge bags→ℚ) (M : BagPM bags)
    (a : ExecutableDP.Bags) (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags)))
    (i : Slot T q) {k : ℕ} (bits : LocalBits V k) :
    typedRefresh ((sourceContext (T:=T) (q:=q) rank parent w a,i),localBitsRep bits)=
      Numbered.set (baseDraw rank parent hb hne hp M k bits).val := by
  exact ExecutableRefresh.refresh_sampleMatching bags rank parent hb hne hp M a ha bits.2

noncomputable local instance : DecidableEq (BagPM bags) := Classical.decEq _
omit [Inhabited (Slot T q)] in
lemma source_run (hq : 0<q) (w : BagEdge bags→ℚ) (M : BagPM bags)
    (a : ExecutableDP.Bags) (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags)))
    {k n : ℕ} (s : Slot T q→BagPM bags) (bits : Fin n→ScanBits V k) :
    let keys := List.ofFn (orderedEnum (Slot T q))
    let c := sourceContext (T:=T) (q:=q) rank parent w a
    let setup := ((c,((Finset.univ : Finset (Slot T q)),base T q)),(keys,Numbered.set (Finset.univ : Finset (BagEdge bags))))
    typedExecute (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
      (setup,stateRep keys (fun i=>Numbered.set (s i).val)))=
      (setup,stateRep keys (fun i=>Numbered.set
        (ladderRun hbags hG rank parent hb hne hp hq w M k n s bits i).val)) := by
  dsimp only
  have hk : ∀ i : Slot T q,i∈List.ofFn (orderedEnum (Slot T q)) := by
    intro i
    simp only [List.mem_ofFn]
    exact ⟨(orderedEnum (Slot T q)).symm i,Equiv.apply_symm_apply _ _⟩
  have hu : ∀ m : BagPM bags,Numbered.set m.val⊆Numbered.set (Finset.univ : Finset (BagEdge bags)) := by
    intro m
    exact Finset.map_subset_map.mpr (Finset.subset_univ _)
  exact scanRun_rep (fun m : BagPM bags=>Numbered.set m.val) localBitsRep
    (sourceContext (T:=T) (q:=q) rank parent w a) (List.ofFn (orderedEnum (Slot T q))) hk _ hu
    guides (base T q) (base_nonempty T q hq) typedGuide (source_guide (T:=T) (q:=q) rank parent w a)
    typedPair typedRefresh (Transport.pairDraw hbags hG w k) (fun _=>baseDraw rank parent hb hne hp M k)
    (fun i j s b=>source_pair (T:=T) (q:=q) hbags hG rank parent w a i j s b) (fun i b=>source_refresh (T:=T) (q:=q) rank parent hb hne hp w M a ha i b) s bits

theorem source_ladder_post : ∃ p : Polynomial ℕ,
    ∀ {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
      {bags : V→Finset L} {G : SimpleGraph L}
      (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)
      (rank : L→ℕ) (parent : L→Option L) (hb : RankedBags bags rank parent)
      (hne : ∀ v,(bags v).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
      {T q : ℕ} [Inhabited (Slot T q)],index (default : Slot T q)=0 → ∀ hq : 0<q,
      ∀ (w : BagEdge bags→ℚ) (M : BagPM bags) (a : ExecutableDP.Bags),
      List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags)) →
      ∀ {k n : ℕ} (s : Slot T q→BagPM bags) (bits : Fin n→ScanBits V k) (t : ℕ),
      let keys := List.ofFn (orderedEnum (Slot T q))
      let c := sourceContext (T:=T) (q:=q) rank parent w a
      let setup := ((c,((Finset.univ : Finset (Slot T q)),base T q)),(keys,Numbered.set (Finset.univ : Finset (BagEdge bags))))
      let x := (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
        (setup,stateRep keys (fun i=>Numbered.set (s i).val)))
      p.eval (TreePost.packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (TreePost.machine executeRealizer.program) (TreePost.packed x) coins).state=none ∧
      (run (TreePost.machine executeRealizer.program) (TreePost.packed x) coins).tape.right₀=
        Turing.ListBlank.mk (TreePost.packed (setup,stateRep keys (fun i=>Numbered.set
          (ladderRun hbags hG rank parent hb hne hp hq w M k n s bits i).val))) := by
  obtain ⟨p,hp⟩:=uniform_ladder_post
  refine ⟨p,fun {V L} _ _ _ _ {bags G} hbags hG rank parent hb hne hparent {T q} _ hz hq w M a ha {k n} s bits t ht coins=>?_⟩
  have h:=hp (I:=Slot T q) hz
    (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
      (((sourceContext (T:=T) (q:=q) rank parent w a,(Finset.univ,base T q)),
        (List.ofFn (orderedEnum (Slot T q)),Numbered.set (Finset.univ : Finset (BagEdge bags)))),
        stateRep (List.ofFn (orderedEnum (Slot T q))) (fun i=>Numbered.set (s i).val))) t ht coins
  rwa [source_run hbags hG rank parent hb hne hparent hq w M a ha s bits] at h
end MatchingFPRAS.NumericLadder

end OAI
