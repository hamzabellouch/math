import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.CappedFold
import OAI.Combinatorics.KMedianRecovery.Encoding.LabelSize
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionBound
import OAI.Combinatorics.KMedianRecovery.Machines.DeleteFold

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordOperations WordList RationalLeaves CanonicalDelete
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

noncomputable def capacityPoly : Polynomial ℕ :=
  let X : Polynomial ℕ:=Polynomial.X
  2*(X*(2*X+2)+(X+X*X)*(2*X+2)+(2*X)*(2*((3*X+1+X*X)*(2*X+2))+2))+6

lemma accBits_bound {m N n : ℕ} {s : Acc (Label (Fin m))}
    (hs : Bounds (fun x=>(BinaryLabel.encode x).length≤N) N n s) (hn : n≤N) :
    (accBits s).length≤capacityPoly.eval N := by
  have he : s.extras.length≤N+N*N := hs.extras.trans (Nat.add_le_add_left (Nat.mul_le_mul_right N hn) N)
  have hv : s.vertices.length≤2*N := hs.vertices.trans (by omega)
  have hw : ∀ H∈s.vertices,H.length≤3*N+1+N*N := fun H hH=>
    (hs.vertex H hH).trans (Nat.add_le_add_left (Nat.mul_le_mul_right N hn) _)
  have hr:=BinaryFiniteContext.labels_length_bounded s.remaining hs.remaining hs.rem_mem
  have he':=BinaryFiniteContext.labels_length_bounded s.extras he hs.ext_mem
  have hV:=encode_le_bound (s.vertices.map labels) ((3*N+1+N*N)*(2*N+2)) (by
    intro w hw'
    obtain ⟨H,hH,rfl⟩:=List.mem_map.mp hw'
    exact BinaryFiniteContext.labels_length_bounded H (hw H hH) (hs.vert_mem H hH))
  simp only [List.length_map] at hV
  have hV':(historyBits s.vertices).length≤(2*N)*(2*((3*N+1+N*N)*(2*N+2))+2) :=
    hV.trans (Nat.mul_le_mul_right _ hv)
  simp only [capacityPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X,
    accBits,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega

noncomputable def capacity : PolynomialCounter capacityPoly := PolynomialCounter.choose capacityPoly
noncomputable def run (x : List Bool) : List Bool := CappedFold.run step (pairBits (capacity.word x,x))
noncomputable def run_computes : PolyComputes run :=
  (capacity.computes.pair id_computes).comp (CappedFold.run_computes step_computes)

def pack {m : ℕ} (base : List Bool) (C : List (Label (Fin m))) (ci : Label (Fin m))
    (U E : List (Label (Fin m))) : List Bool :=
  Fold.pack (labels U) (contextBits base (labels C) (BinaryLabel.encode ci)) (accBits ⟨U,E,[]⟩)

lemma pack_bounds {m : ℕ} (base : List Bool) (C : List (Label (Fin m))) (ci : Label (Fin m))
    (U E : List (Label (Fin m))) :
    base.length≤(pack base C ci U E).length ∧
    (labels C).length≤(pack base C ci U E).length ∧
    (BinaryLabel.encode ci).length≤(pack base C ci U E).length ∧
    (labels U).length≤(pack base C ci U E).length ∧
    (labels E).length≤(pack base C ci U E).length := by
  have hb : base.length≤(contextBits base (labels C) (BinaryLabel.encode ci)).length :=
    member_length (List.mem_cons_self ..)
  have hC : (labels C).length≤(contextBits base (labels C) (BinaryLabel.encode ci)).length :=
    member_length (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hi : (BinaryLabel.encode ci).length≤(contextBits base (labels C) (BinaryLabel.encode ci)).length :=
    member_length (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hE : (labels E).length≤(accBits (⟨U,E,[]⟩ : Acc (Label (Fin m)))).length :=
    member_length (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only [pack,Fold.length_pack]
  omega

lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (copy : Label (Fin m) → Label (Fin m))
    (C : List (Label (Fin m))) (i : Label (Fin m)) (U E : List (Label (Fin m))) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) C (copy i) U E)=
      accBits ⟨[],(CanonicalMergePath.deleteSuffix
        (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q copy C i U E).1,
        (CanonicalMergePath.deleteSuffix
        (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q copy C i U E).2⟩ := by
  let base:=BinaryFiniteContext.pack distance loc F Q v z lam
  let x:=pack base C (copy i) U E
  let N:=x.length
  obtain ⟨hb,hC,hi,hU,hE⟩:=pack_bounds base C (copy i) U E
  have hc : ∀ W,(FiniteLabelContinuation.complete loc (rows distance) F v z lam W).length≤N ∧
      ∀ j∈FiniteLabelContinuation.complete loc (rows distance) F v z lam W,(BinaryLabel.encode j).length≤N := by
    intro W
    obtain ⟨hlen,hmem⟩:=FiniteLabelContinuation.complete_events loc (rows distance) F W v z lam
    have hF : (setBits F).length≤N := (BinaryFiniteContext.pack_F_bound distance loc F Q v z lam).trans hb
    exact ⟨hlen.trans ((BinaryFiniteContext.card_setBits_le F).trans hF),
      fun j hj=>(BinaryFiniteContext.member_setBits_length (hmem j hj)).trans hF⟩
  have hClen : C.length≤N := (BinaryFiniteContext.length_labels_le C).trans hC
  have hUlen : U.length≤N := (BinaryFiniteContext.length_labels_le U).trans hU
  have hCm : ∀ j∈C,(BinaryLabel.encode j).length≤N :=
    fun j hj=>(BinaryFiniteContext.member_labels_length hj).trans hC
  have hs : Bounds (fun j=>(BinaryLabel.encode j).length≤N) N 0 (⟨U,E,[]⟩ : Acc (Label (Fin m))) := by
    refine ⟨hUlen,?_,?_,?_,?_,?_,?_⟩
    · simpa only [Nat.zero_mul,Nat.add_zero] using (BinaryFiniteContext.length_labels_le E).trans hE
    · exact Nat.zero_le _
    · intro H hH; exact False.elim (List.not_mem_nil hH)
    · exact fun j hj=>(BinaryFiniteContext.member_labels_length hj).trans hU
    · exact fun j hj=>(BinaryFiniteContext.member_labels_length hj).trans hE
    · intro H hH; exact False.elim (List.not_mem_nil hH)
  have ht:=CappedFold.run_typed accBits BinaryLabel.encode
    (CanonicalDelete.step (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q C (copy i)) step
    (contextBits base (labels C) (BinaryLabel.encode (copy i))) (capacity.word x)
    (fun s a=>step_pack distance loc F Q v z lam C (copy i) a s) (⟨U,E,[]⟩ : Acc (Label (Fin m))) U
  have heq:=ht (by
    intro n
    rw [capacity.word_length]
    apply accBits_bound
    · simpa only [Nat.zero_add] using hs.fold hClen hCm hi hc (U.take n)
    · simp only [List.length_take]; exact (Nat.min_le_right n U.length).trans hUlen)
  change run x = _ at heq
  rw [CanonicalDelete.fold_result,List.nil_append] at heq
  exact heq
end MetricKMedianRecovery.BitMachine.BinaryDelete

namespace MetricKMedianRecovery.BitMachine.BinaryAdvance
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

def pack {m : ℕ} (base : List Bool) (C U : List (Label (Fin m))) (i ci : Label (Fin m)) : List Bool :=
  encode [base,labels C,labels U,BinaryLabel.encode i,BinaryLabel.encode ci]
noncomputable def deletionInput (x : List Bool) : List Bool :=
  Fold.pack (field 2 x) (encode [field 0 x,field 1 x,field 4 x]) (encode [field 2 x,[],[]])
noncomputable def deletionInput_computes : PolyComputes deletionInput := by
  have hctx := list_computes [field 0,field 1,field 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl <;> exact ⟨field_computes _⟩)
  have hacc := list_computes [field 2,fun _=>[],fun _=>[]] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨field_computes _⟩
    all_goals exact ⟨const_computes []⟩)
  exact Fold.pack_computes (field_computes 2) hctx hacc
noncomputable def deleted : List Bool → List Bool := BinaryDelete.run ∘ deletionInput
noncomputable def deleted_computes : PolyComputes deleted := deletionInput_computes.comp BinaryDelete.run_computes
noncomputable def suffix : List Bool → List Bool := field 1 ∘ deleted
noncomputable def suffix_computes : PolyComputes suffix := deleted_computes.comp (field_computes 1)
noncomputable def firstVertex (x : List Bool) : List Bool := field 1 x++field 2 x++WordList.cons (field 4 x) []
noncomputable def firstVertex_computes : PolyComputes firstVertex :=
  ((field_computes 1).append (field_computes 2)).append (cons_computes (field_computes 4) (const_computes []))
noncomputable def lastVertex (x : List Bool) : List Bool := field 1 x++WordList.cons (field 3 x) (suffix x)
noncomputable def lastVertex_computes : PolyComputes lastVertex :=
  (field_computes 1).append (cons_computes (field_computes 3) suffix_computes)
noncomputable def vertices (x : List Bool) : List Bool :=
  WordList.cons (firstVertex x) (field 2 (deleted x)++WordList.cons (lastVertex x) [])
noncomputable def vertices_computes : PolyComputes vertices :=
  cons_computes firstVertex_computes ((deleted_computes.comp (field_computes 2)).append
    (cons_computes lastVertex_computes (const_computes [])))
noncomputable def run (x : List Bool) : List Bool := encode [suffix x,vertices x]
noncomputable def run_computes : PolyComputes run := list_computes [suffix,vertices] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl
  · exact ⟨suffix_computes⟩
  · exact ⟨vertices_computes⟩)

lemma deleted_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (copy : Label (Fin m) → Label (Fin m))
    (C U : List (Label (Fin m))) (i : Label (Fin m)) :
    deleted (pack (BinaryFiniteContext.pack distance loc F Q v z lam) C U i (copy i))=
    BinaryDelete.accBits ⟨[],(CanonicalMergePath.deleteSuffix
      (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q copy C i U []).1,
      (CanonicalMergePath.deleteSuffix (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q copy C i U []).2⟩ := by
  unfold deleted deletionInput pack
  simp only [Function.comp_apply,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  exact BinaryDelete.run_pack distance loc F Q v z lam copy C i U []
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (copy : Label (Fin m) → Label (Fin m))
    (C U : List (Label (Fin m))) (i : Label (Fin m)) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) C U i (copy i))=
    encode [labels (CanonicalMergePath.advancePrefix
      (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q copy C U i).1,
      historyBits (CanonicalMergePath.advancePrefix
      (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q copy C U i).2] := by
  simp only [run,vertices,lastVertex,firstVertex,suffix,Function.comp_apply,deleted_pack]
  simp only [pack,BinaryDelete.accBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [CanonicalMergePath.advancePrefix,BinaryFiniteContext.labels_append,BinaryFiniteContext.labels_cons,
    BinaryFiniteContext.labels_nil,BinaryFiniteMachine.historyBits_cons,BinaryFiniteMachine.historyBits_append,
    BinaryFiniteMachine.historyBits_nil]
end MetricKMedianRecovery.BitMachine.BinaryAdvance

end OAI
