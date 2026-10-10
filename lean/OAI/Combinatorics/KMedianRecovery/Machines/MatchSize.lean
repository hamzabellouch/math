import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.PlanResult
import OAI.Combinatorics.KMedianRecovery.Machines.MatchFold

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

noncomputable def capacityPoly : Polynomial ℕ :=
  let X : Polynomial ℕ:=Polynomial.X
  2*(2*X*(2*X+2)+X*(X+2)*(2*((X+1)*(2*X+2))+2))+6
noncomputable def capacity : PolynomialCounter capacityPoly := PolynomialCounter.choose capacityPoly
lemma accBits_bound {m N : ℕ} {s : Acc (Label (Fin m))}
    (hC : s.front.length≤N) (hU : s.rest.length≤N) (hV : s.vertices.length≤N*(N+2))
    (hW : ∀ H∈s.vertices,H.length≤N+1)
    (hmC : ∀ x∈s.front,(BinaryLabel.encode x).length≤N)
    (hmU : ∀ x∈s.rest,(BinaryLabel.encode x).length≤N)
    (hmV : ∀ H∈s.vertices,∀ x∈H,(BinaryLabel.encode x).length≤N) :
    (accBits s).length≤capacityPoly.eval N := by
  have hC':=BinaryFiniteContext.labels_length_bounded s.front hC hmC
  have hU':=BinaryFiniteContext.labels_length_bounded s.rest hU hmU
  have hV':=(encode_le_bound (s.vertices.map labels) ((N+1)*(2*N+2)) (by
    intro w hw
    obtain ⟨H,hH,rfl⟩:=List.mem_map.mp hw
    exact BinaryFiniteContext.labels_length_bounded H (hW H hH) (hmV H hH)))
  simp only [List.length_map] at hV'
  have hhist : (historyBits s.vertices).length≤N*(N+2)*(2*((N+1)*(2*N+2))+2) :=
    hV'.trans (Nat.mul_le_mul_right _ hV)
  simp only [capacityPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_one,Polynomial.eval_X,accBits,length_encode,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  simp only [Nat.mul_assoc] at *
  omega
noncomputable def run (x : List Bool) : List Bool := CappedFold.run step (pairBits (capacity.word x,x))
noncomputable def run_computes : PolyComputes run :=
  (capacity.computes.pair id_computes).comp (CappedFold.run_computes step_computes)
def pack {m : ℕ} (base : List Bool) (key : ℕ) (F : Finset (Label (Fin m)))
    (C U T : List (Label (Fin m))) : List Bool :=
  Fold.pack (labels T) (contextBits base key F) (accBits ⟨C,U,[]⟩)
lemma pack_bounds {m : ℕ} (base : List Bool) (key : ℕ) (F : Finset (Label (Fin m)))
    (C U T : List (Label (Fin m))) :
    base.length≤(pack base key F C U T).length ∧
    (labels ((BinaryLabel.orderedSort F).map (copy key))).length≤(pack base key F C U T).length ∧
    (labels T).length≤(pack base key F C U T).length := by
  have hb : base.length≤(contextBits base key F).length := member_length (List.mem_cons_self ..)
  have hc : (labels ((BinaryLabel.orderedSort F).map (copy key))).length≤(contextBits base key F).length :=
    member_length (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  simp only [pack,Fold.length_pack]
  omega

lemma run_pack {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
    (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F B Q : Finset (Label (Fin m))) (v z lam : ℚ) (eta : ℝ) (key : ℕ)
    (hc : CorrectCompletion loc F (v:ℝ) z lam (FiniteLabelContinuation.complete loc (rows distance) F v z lam))
    (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hz : (0:ℝ)<z) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) z Q i≤lam)
    (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
    (C U T : List (Label (Fin m))) (hCr : ∀ i∈C,i∈F) (hUr : ∀ i∈U,i∈F) (hTr : ∀ i∈T,i∈F)
    (htarget : Prefix loc F B v z lam eta Q (C++T)) (hcur : Valid loc F B Q v z lam eta (C++U)) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key F C U T)=
      accBits ⟨C++T,(matchPrefix (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) C U T).1,
        (matchPrefix (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) C U T).2⟩ := by
  let base:=BinaryFiniteContext.pack distance loc F Q v z lam
  let x:=pack base key F C U T
  let N:=x.length
  obtain ⟨hb,hcopy,hT⟩:=pack_bounds base key F C U T
  have hFB : (setBits F).length≤N := (BinaryFiniteContext.pack_F_bound distance loc F Q v z lam).trans hb
  have hFcard : F.card≤N := (BinaryFiniteContext.card_setBits_le F).trans hFB
  have hTlen : T.length≤N := (BinaryFiniteContext.length_labels_le T).trans hT
  have hFm : ∀ i∈F,(BinaryLabel.encode i).length≤N :=
    fun i hi=>(BinaryFiniteContext.member_setBits_length hi).trans hFB
  have hcm : ∀ i∈F,(BinaryLabel.encode (copy key i)).length≤N := by
    intro i hi
    apply (BinaryFiniteContext.member_labels_length ?_).trans hcopy
    exact List.mem_map.mpr ⟨i,(Finset.mem_sort _).mpr hi,rfl⟩
  have ht:=CappedFold.run_typed accBits BinaryLabel.encode
    (CanonicalMatch.step (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key)) step
    (contextBits base key F) (capacity.word x) (step_pack distance loc F Q v z lam key) (⟨C,U,[]⟩ : Acc (Label (Fin m))) T
  have heq:=ht (by
    intro n
    rw [capacity.word_length]
    obtain ⟨hC,hU,hV,hW,hmC,hmU,hmV⟩:=CanonicalMatch.fold_bounds loc F B Q (copy key)
      v z lam eta _ hc hv hvsmall hz hlam heta hQ hdis hrow hfresh hco C U (T.take n) hCr hUr
      (fun i hi=>hTr i (List.mem_of_mem_take hi))
      (htarget.sublist ((List.take_sublist n T).append_left C)) hcur hFm hcm
    apply accBits_bound (hC.trans hFcard) (hU.trans hFcard) _ _ hmC hmU hmV
    · apply hV.trans
      exact Nat.mul_le_mul ((by simp only [List.length_take]; exact (Nat.min_le_right n T.length).trans hTlen))
        (Nat.add_le_add_right hFcard 2)
    · exact fun H hH=>(hW H hH).trans (Nat.add_le_add_right hFcard 1))
  change run x = _ at heq
  rw [CanonicalMatch.fold_result,List.nil_append] at heq
  exact heq
end MetricKMedianRecovery.BitMachine.BinaryMatch

namespace MetricKMedianRecovery.BitMachine.BinaryRegular
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

def pack {m : ℕ} (base : List Bool) (key : ℕ) (H J : List (Label (Fin m))) : List Bool :=
  encode [base,key.bits,labels H,labels J]
noncomputable def poolInput (x : List Bool) : List Bool := pairBits (field 1 x,field 2 (field 0 x))
noncomputable def poolInput_computes : PolyComputes poolInput :=
  (field_computes 1).pair ((field_computes 0).comp (field_computes 2))
noncomputable def pool : List Bool → List Bool := mapWith BinaryLabel.copied ∘ poolInput
noncomputable def pool_computes : PolyComputes pool := poolInput_computes.comp (mapWith_computes BinaryLabel.copied_computes)
noncomputable def context (x : List Bool) : List Bool := encode [field 0 x,field 1 x,pool x]
noncomputable def context_computes : PolyComputes context := list_computes [field 0,field 1,pool] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨field_computes _⟩
  · exact ⟨field_computes _⟩
  · exact ⟨pool_computes⟩)
noncomputable def state0 (x : List Bool) : List Bool := encode [[],field 3 x,[]]
noncomputable def state0_computes : PolyComputes state0 := list_computes [fun _=>[],field 3,fun _=>[]] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨const_computes []⟩
  · exact ⟨field_computes _⟩
  · exact ⟨const_computes []⟩)
noncomputable def matchInput (x : List Bool) : List Bool := Fold.pack (field 2 x) (context x) (state0 x)
noncomputable def matchInput_computes : PolyComputes matchInput := Fold.pack_computes (field_computes 2) context_computes state0_computes
noncomputable def matched : List Bool → List Bool := BinaryMatch.run ∘ matchInput
noncomputable def matched_computes : PolyComputes matched := matchInput_computes.comp BinaryMatch.run_computes
noncomputable def prunedInput (x : List Bool) : List Bool := pairBits (field 2 x,field 1 (matched x))
noncomputable def prunedInput_computes : PolyComputes prunedInput := by
  unfold prunedInput
  simpa only [Function.comp_def] using (field_computes 2).pair (matched_computes.comp (field_computes 1))
noncomputable def run (x : List Bool) : List Bool := field 2 (matched x)++BinarySuffix.prune (prunedInput x)
noncomputable def run_computes : PolyComputes run := by
  have composeComputes (matchedFunction prunedFunction : List Bool → List Bool)
      (matchedComputes : PolyComputes matchedFunction) (prunedComputes : PolyComputes prunedFunction) :
      PolyComputes (fun input=>field 2 (matchedFunction input)++BinarySuffix.prune (prunedFunction input)) := by
    simpa only [Function.comp_def] using
      (matchedComputes.comp (field_computes 2)).append (prunedComputes.comp BinarySuffix.prune_computes)
  exact composeComputes matched prunedInput matched_computes prunedInput_computes
lemma base_F {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    field 2 (BinaryFiniteContext.pack distance loc F Q v z lam)=setBits F := by
  simp only [BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma pool_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key : ℕ) (H J : List (Label (Fin m))) :
    pool (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key H J)=
      labels ((BinaryLabel.orderedSort F).map (copy key)) := by
  simp only [pool,Function.comp_apply,poolInput,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,base_F]
  simp only [setBits,labels,mapWith_encode,List.map_map,Function.comp_def,BinaryLabel.copied_pack]
lemma matchInput_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key : ℕ) (H J : List (Label (Fin m))) :
    matchInput (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key H J)=
      BinaryMatch.pack (BinaryFiniteContext.pack distance loc F Q v z lam) key F [] J H := by
  simp only [matchInput,context,state0]
  rw [pool_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rfl
lemma run_pack {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
    (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F B Q : Finset (Label (Fin m))) (v z lam : ℚ) (eta : ℝ) (key : ℕ)
    (hc : CorrectCompletion loc F (v:ℝ) z lam (FiniteLabelContinuation.complete loc (rows distance) F v z lam))
    (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hz : (0:ℝ)<z) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) z Q i≤lam)
    (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
    (H J : List (Label (Fin m))) (hHr : ∀ i∈H,i∈F) (hJr : ∀ i∈J,i∈F)
    (hH : Valid loc F B Q v z lam eta H) (hJ : Valid loc F B Q v z lam eta J) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key H J)=
      historyBits (regularPath (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) H J) := by
  have hm:=BinaryMatch.run_pack distance loc F B Q v z lam eta key hc hv hvsmall hz hlam heta hQ hdis hrow hfresh hco
    [] J H (by intro i hi; exact (List.not_mem_nil hi).elim) hJr hHr
    (by simpa only [List.nil_append] using hH.1) (by simpa only [List.nil_append] using hJ)
  simp only [run,prunedInput,matched,Function.comp_apply,matchInput_pack,hm]
  simp only [pack,BinaryMatch.accBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [BinarySuffix.prune_pack,←BinaryFiniteMachine.historyBits_append]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryRegular

end OAI
