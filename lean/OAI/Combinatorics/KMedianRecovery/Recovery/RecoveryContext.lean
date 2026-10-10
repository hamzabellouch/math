import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.ObservableCapacity

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
def pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
    (s : RationalSampling.State n) (m : ℕ) (extra raw : List Bool) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,
    BinaryRational.encode Δ,BinarySamplingState.encode s,List.replicate n true,List.replicate m true,extra,raw]
def choiceBits (q c b : ℕ) : List Bool := pairBits (q.bits,pairBits (c.bits,b.bits))
noncomputable def qbits : List Bool→List Bool := extractPrefix ∘ discardPrefix
noncomputable def cbits : List Bool→List Bool := extractPrefix ∘ discardPrefix ∘ discardPrefix
noncomputable def bbits : List Bool→List Bool := UnaryResources.inc ∘ discardPrefix ∘ discardPrefix ∘ discardPrefix
noncomputable def qbits_computes : PolyComputes qbits := discardPrefix_computes.comp extractPrefix_computes
noncomputable def cbits_computes : PolyComputes cbits := (discardPrefix_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def bbits_computes : PolyComputes bbits := ((discardPrefix_computes.comp discardPrefix_computes).comp discardPrefix_computes).comp UnaryResources.inc_computes
noncomputable def src (j : ℕ) : List Bool→List Bool := field j ∘ extractPrefix
noncomputable def src_computes (j : ℕ) : PolyComputes (src j) := extractPrefix_computes.comp (field_computes j)
noncomputable def cword (x : List Bool) : List Bool := RawTake.run (pairBits (cbits x,src 6 x))
noncomputable def bword (x : List Bool) : List Bool := RawTake.run (pairBits (bbits x,src 7 x))
attribute [local irreducible] RawTake.run BinaryEllipsoidInitial.indices
noncomputable def cword_computes : PolyComputes cword := (cbits_computes.pair (src_computes 6)).comp RawTake.run_computes
noncomputable def bword_computes : PolyComputes bword := (bbits_computes.pair (src_computes 7)).comp RawTake.run_computes
noncomputable def zeros (x : List Bool) : List Bool := mapWith (fun _=>[]) (pairBits ([],BinaryEllipsoidInitial.indices (src 6 x)))
attribute [local irreducible] mapWith
noncomputable def zeros_computes : PolyComputes zeros :=
  PolyComputes.comp (f := fun input=>pairBits ([],BinaryEllipsoidInitial.indices (src 6 input)))
    (g := mapWith (fun _=>[]))
    ((const_computes []).pair ((src_computes 6).comp BinaryEllipsoidInitial.indices_computes))
    (mapWith_computes (const_computes []))
noncomputable def labels (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (bword x)
noncomputable def labels_computes : PolyComputes labels := bword_computes.comp BinaryEllipsoidInitial.indices_computes
noncomputable def context (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 4 x,src 5 x,zeros x,zeros x,labels x,qbits x,cword x,src 8 x]
attribute [local irreducible] src zeros labels qbits cword bword
noncomputable def context_computes : PolyComputes context := list_computes
  [src 0,src 1,src 2,src 3,src 4,src 5,zeros,zeros,labels,qbits,cword,src 8] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨zeros_computes⟩ | exact ⟨labels_computes⟩ | exact ⟨qbits_computes⟩ | exact ⟨cword_computes⟩)
noncomputable def zeroContext (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 4 x,src 5 x,zeros x,zeros x,encode [[]],qbits x,[],src 8 x]
noncomputable def zeroContext_computes : PolyComputes zeroContext := list_computes
  [src 0,src 1,src 2,src 3,src 4,src 5,zeros,zeros,fun _=>encode [[]],qbits,fun _=>[],src 8] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨zeros_computes⟩ | exact ⟨qbits_computes⟩ | exact ⟨const_computes _⟩)
section Exact
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s : RationalSampling.State n) (m : ℕ) (extra raw : List Bool) (q c b : ℕ)
local notation "data" => pairBits (pack δ D F S Δ s m extra raw,choiceBits q c b)
lemma qbits_pack : qbits data=q.bits := by simp only [qbits,choiceBits,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
lemma cbits_pack : cbits data=c.bits := by simp only [cbits,choiceBits,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
lemma bbits_pack : bbits data=(b+1).bits := by simp only [bbits,choiceBits,Function.comp_apply,discardPrefix_pairBits,UnaryResources.inc,value_bits]
lemma cword_pack (hc : c ≤ n) : cword data=List.replicate c true := by
  rw [cword,cbits_pack]
  simp only [src,Function.comp_apply,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,RawTake.run_pack,List.take_replicate,min_eq_left hc]
lemma bword_pack (hb : b + 1 ≤ m) : bword data=List.replicate (b+1) true := by
  rw [bword,bbits_pack]
  simp only [src,Function.comp_apply,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,RawTake.run_pack,List.take_replicate,min_eq_left hb]
lemma zeros_pack (a : ℕ) [NeZero a] : zeros data=BinaryFinSet.table (fun _:Fin n=>(0:Fin a)) := by
  simp only [zeros,src,Function.comp_apply,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryEllipsoidInitial.indices_replicate,mapWith_ofFn,BinaryFinSet.table]
  rfl
lemma labels_pack (hb : b + 1 ≤ m) : labels data=BinaryFinSet.table (id : Fin (b+1)→Fin (b+1)) := by
  rw [labels,bword_pack δ D F S Δ s m extra raw q c b hb,BinaryEllipsoidInitial.indices_replicate]
  rfl
lemma context_pack (hc : c ≤ n) (hb : b + 1 ≤ m) : context data=
    BinaryBranchContext.pack δ D F S Δ s (fun _=>0) (fun _=>(0:Fin (b+1))) q c extra := by
  rw [context,zeros_pack δ D F S Δ s m extra raw q c b 3,
    labels_pack δ D F S Δ s m extra raw q c b hb,qbits_pack,cword_pack δ D F S Δ s m extra raw q c b hc]
  simp only [src,Function.comp_apply,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryBranchContext.pack]
  rfl
lemma zeroContext_pack : zeroContext data=BinaryZeroBranch.pack δ D F S Δ s (fun _=>0) q extra := by
  rw [zeroContext,zeros_pack δ D F S Δ s m extra raw q c b 3,qbits_pack]
  simp only [src,Function.comp_apply,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryZeroBranch.pack,BinaryBranchContext.pack]
  rfl
end Exact
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
