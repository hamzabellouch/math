import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartProgram
import OAI.Combinatorics.ContingencyTables.Machines.FiniteVaryingObservable

namespace OAI

/-! # Exact disjoint-word semantics of the physical restart loop -/
namespace ContingencyTables.CompanionRestartProgram
open FirstSuccess FiniteObservableTransport MatchingFPRAS DensePrograms CommonBasesFPRAS
open scoped BigOperators Classical

def widthAt (base : List Stage×List ℕ) (i : ℕ) : ℕ := indexedWidth ((base,[]),i)

lemma widths_ofFn (base : List Stage×List ℕ) (bits : List Bool) :
    widths (base,bits)=List.ofFn (fun i : Fin base.1.length => widthAt base i.val) := by
  unfold widths indices
  rw [DirectedBFSCode.range_eq_map]
  simp only [List.map_map,Function.comp_def]
  change (List.finRange base.1.length).map (fun i => widthAt base i.val)=_
  exact List.ofFn_eq_map.symm

lemma stageWord_ofFn (base : List Stage×List ℕ)
    (bits : Fin (∑ i : Fin base.1.length,widthAt base i.val) → Bool)
    (i : Fin base.1.length) :
    stageWord ((base,List.ofFn bits),i.val)=
      List.ofFn (varyingWordEquiv (widthAt base) base.1.length bits i) := by
  unfold stageWord
  rw [widths_ofFn]
  exact dependentChunk_ofFn (fun i : Fin base.1.length => widthAt base i.val) bits i

def detachedStep (base : List Stage×List ℕ) (i : ℕ) (code : List ℕ)
    (bits : List Bool) : List ℕ :=
  ProfilePrograms.capView ((base.2.length,1),
    CompanionRestartStageProgram.output ((base.1.getD i default,code),bits))

lemma next_detached (base : List Stage×List ℕ) (allBits : List Bool) (i : ℕ) (code : List ℕ) :
    next (i,((base,allBits),code))=
      detachedStep base i code (stageWord ((base,allBits),i)) := rfl

lemma walk_eq (input : Input) (is : List ℕ) (code : List ℕ) :
    walk ((input,code),is)=
      (input,is.foldl (fun code i => next (i,(input,code))) code) := by
  induction is generalizing code with
  | nil => rfl
  | cons i is ih =>
    simpa only [walk,List.foldl_cons,advance] using ih (next (i,(input,code)))

 private lemma fold_range_varying {C : Type*} (width : ℕ → ℕ)
    (F : ℕ → C → C) (G : (i : ℕ) → C → (Fin (width i) → Bool) → C)
    (c : C) (N : ℕ) (words : VaryingWords width N)
    (h : ∀ i : Fin N,∀ c,F i.val c=G i.val c (words i)) :
    (List.range N).foldl (fun c i => F i c) c=varyingWalk width G c N words := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,varyingWalk]
    have hp := ih (Fin.init words) (fun i c => h i.castSucc c)
    rw [hp]
    exact h (Fin.last N) _

/-- The bounded list program consumes exactly its independent stage
blocks. No assumption about the encoded states is needed here. -/
theorem output_varyingWalk (base : List Stage×List ℕ)
    (bits : Fin (∑ i : Fin base.1.length,widthAt base i.val) → Bool) :
    output (base,List.ofFn bits)=
      varyingWalk (widthAt base)
        (fun i code word => detachedStep base i code (List.ofFn word))
        base.2 base.1.length (varyingWordEquiv (widthAt base) base.1.length bits) := by
  unfold output
  rw [walk_eq]
  change (List.range base.1.length).foldl
    (fun code i => next (i,((base,List.ofFn bits),code))) base.2=_
  apply fold_range_varying
  intro i code
  rw [next_detached,stageWord_ofFn]

noncomputable section

/-- Conditional laws compose across the actual disjoint variable-width
blocks, even when the source and encoded state spaces have different sizes. -/
theorem output_sameLaw {Z : Type*} (base : List Stage×List ℕ) (v : ℕ → ℕ)
    (G : (i : ℕ) → Z → (Fin (v i) → Bool) → Z) (e : Z → List ℕ)
    (z : Z) (hz : base.2=e z)
    (h : ∀ i,i < base.1.length → ∀ s,SameLaw
      (fun bits : Fin (widthAt base i) → Bool => detachedStep base i (e s) (List.ofFn bits))
      (fun bits => e (G i s bits))) :
    SameLaw (fun bits : Fin (∑ i : Fin base.1.length,widthAt base i.val) → Bool =>
      output (base,List.ofFn bits))
      (fun bits : Fin (∑ i : Fin base.1.length,v i.val) → Bool =>
        e (varyingWalk v G z base.1.length (varyingWordEquiv v base.1.length bits))) := by
  let F := fun (i : ℕ) (code : List ℕ) (bits : Fin (widthAt base i) → Bool) =>
    detachedStep base i code (List.ofFn bits)
  have hh := varyingWalk_sameLaw_prefix (widthAt base) v F G e z base.1.length h
  intro phi
  have hu := uniformAverage_equiv (varyingWordEquiv (widthAt base) base.1.length)
    (fun words => phi (varyingWalk (widthAt base) F (e z) base.1.length words))
  have hv := uniformAverage_equiv (varyingWordEquiv v base.1.length)
    (fun words => phi (e (varyingWalk v G z base.1.length words)))
  calc
    _ = uniformAverage (fun bits => phi (varyingWalk (widthAt base) F (e z) base.1.length
        (varyingWordEquiv (widthAt base) base.1.length bits))) := by
      apply congrArg uniformAverage
      funext bits
      dsimp only
      rw [output_varyingWalk,hz]
    _ = uniformAverage (fun words => phi (varyingWalk (widthAt base) F (e z) base.1.length words)) := hu
    _ = uniformAverage (fun words => phi (e (varyingWalk v G z base.1.length words))) := hh phi
    _ = _ := hv.symm

end
end ContingencyTables.CompanionRestartProgram

end OAI
