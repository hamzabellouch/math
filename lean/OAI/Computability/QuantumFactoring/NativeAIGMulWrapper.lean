import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGMulBounded
import OAI.Computability.QuantumFactoring.NativeAIGMulProcedure

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

abbrev BinaryState:={s : AddState // s.val.lhs.length=s.val.rhs.length}
def binaryStateCode (s : BinaryState) : List Bool:=addStateCode s.val
lemma RefsBound.zeros {B w : ℕ} (h : w≤B) : RefsBound B (List.replicate w (0,false)) := by
  refine ⟨by simpa,?_⟩
  intro a ha
  have he:=List.eq_of_mem_replicate ha
  simpa only [he] using Nat.zero_le B

def mulFirstInput (s : BinaryState) : AddState:=
  ⟨⟨s.val.val.budget,s.val.val.graph,s.val.val.lhs,List.replicate s.val.val.lhs.length (0,false),
    0,s.val.val.rhs.headD (0,false),[]⟩,
  s.val.property.1,s.val.property.2.1,RefsBound.zeros s.val.property.2.1.1,Nat.zero_le _,
  by simpa using s.val.property.2.2.1.get 0,Nat.zero_le _,by intro a ha;cases ha⟩
def mulFirst (s : BinaryState) : AddState:=ifVecState (mulFirstInput s)
lemma mulFirst_budget (s : BinaryState) : (mulFirst s).val.budget=s.val.val.budget+3*s.val.val.lhs.length:=
  ifVecState_budget _
lemma mulFirst_length (s : BinaryState) : (mulFirst s).val.output.length=s.val.val.lhs.length:=
  ifVecState_length _
lemma mulFirst_value (s : BinaryState) : ((mulFirst s).val.graph,(mulFirst s).val.output)=
    ifVec s.val.val.graph (s.val.val.rhs.headD (0,false)) s.val.val.lhs
      (List.replicate s.val.val.lhs.length (0,false)):=ifVecState_value _
def initializeMul (s : BinaryState) : MulState:=
  ⟨⟨(mulFirst s).val.budget+1,(mulFirst s).val.graph,s.val.val.lhs,s.val.val.rhs,1,(0,false),
      (mulFirst s).val.output⟩,
  ⟨(mulFirst s).property.1.mono (by dsimp only;omega),
    s.val.property.2.1.mono (by dsimp only;rw [mulFirst_budget];omega),
    s.val.property.2.2.1.mono (by dsimp only;rw [mulFirst_budget];omega),by dsimp only;omega,Nat.zero_le _,
    (mulFirst s).property.2.2.2.2.2.mono (by dsimp only;omega)⟩,s.property,mulFirst_length s⟩
def mulBlastState (s : BinaryState) : MulState:=(mulStep^[s.val.val.lhs.length-1]) (initializeMul s)
lemma mulBlastState_value (s : BinaryState) :
    ((mulBlastState s).val.graph,(mulBlastState s).val.output)=
      mulBlast s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  rw [mulBlastState,mulStep_iterate_loop]
  have hh:=mulFirst_value s
  have h1:=congrArg Prod.fst hh
  have h2:=congrArg Prod.snd hh
  dsimp only [Prod.fst] at h1
  dsimp only [Prod.snd] at h2
  dsimp only [initializeMul]
  rw [h1,h2,mulBlast]
  split
  · rename_i hz
    have hl:=List.length_eq_zero_iff.mp hz
    simp only [hl,List.length_nil,Nat.zero_sub,List.replicate_zero,ifVec,ifLoop,mulLoop]
  · rfl

def swapBinary (s : BinaryState) : BinaryState:=⟨swapAdd s.val,s.property.symm⟩
def mulState (s : BinaryState) : MulState:=
  if countKnown s.val.val.graph s.val.val.lhs<countKnown s.val.val.graph s.val.val.rhs then
    mulBlastState s else mulBlastState (swapBinary s)
lemma mulState_value (s : BinaryState) : ((mulState s).val.graph,(mulState s).val.output)=
    mul s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  unfold mulState mul
  split <;> exact mulBlastState_value _
lemma mulBlastState_budget (s : BinaryState) : (mulBlastState s).val.budget=
    s.val.val.budget+3*s.val.val.lhs.length+1+(16*s.val.val.lhs.length+1)*(s.val.val.lhs.length-1) := by
  rw [mulBlastState,mulStep_iterate_budget]
  dsimp only [initializeMul]
  rw [mulFirst_budget]
lemma mulState_budget (s : BinaryState) : (mulState s).val.budget=
    s.val.val.budget+3*s.val.val.lhs.length+1+(16*s.val.val.lhs.length+1)*(s.val.val.lhs.length-1) := by
  unfold mulState
  split
  · exact mulBlastState_budget s
  · rw [mulBlastState_budget]
    change s.val.val.budget+3*s.val.val.rhs.length+1+(16*s.val.val.rhs.length+1)*(s.val.val.rhs.length-1)=_
    rw [s.property]
lemma mulState_length (s : BinaryState) : (mulState s).val.output.length=s.val.val.lhs.length := by
  have hh:=(mulState s).property.2.2
  rw [hh]
  unfold mulState
  split <;> rw [mulBlastState,mulStep_iterate_lhs]
  · rfl
  · exact s.property.symm

namespace Emission
noncomputable def binaryGraphP : Procedure binaryStateCode graphCode (fun s=>s.val.val.graph):=
  addGraphP.precompose (fun s:BinaryState=>s.val.val)
noncomputable def binaryLhsP : Procedure binaryStateCode (listCode refCode) (fun s=>s.val.val.lhs):=
  addLhsP.precompose (fun s:BinaryState=>s.val.val)
noncomputable def binaryRhsP : Procedure binaryStateCode (listCode refCode) (fun s=>s.val.val.rhs):=
  addRhsP.precompose (fun s:BinaryState=>s.val.val)
noncomputable def zerosP : Procedure (listCode refCode) (listCode refCode)
    (fun xs=>List.replicate xs.length (0,false)) :=
  (listMap (0,false) (0,false) (Procedure.constant refCode refCode (0,false))).congrFun (by
    intro xs;exact List.map_const')
noncomputable def mulFirstInputP : Procedure binaryStateCode addStateCode mulFirstInput := by
  let b:=((first unaryCode addTail1).comp addViewP).precompose (fun s:BinaryState=>s.val.val)
  let c:=(listHead refCode (0,false)).comp binaryRhsP
  exact (packAddP.comp (b.pair (binaryGraphP.pair (binaryLhsP.pair ((zerosP.comp binaryLhsP).pair
    ((Procedure.constant _ Nat.bits 0).pair (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result
    (by intro s;rfl)
noncomputable def mulFirstP : Procedure binaryStateCode addStateCode mulFirst:=ifVecStateP.comp mulFirstInputP
noncomputable def initializeMulP : Procedure binaryStateCode mulStateCode initializeMul := by
  let f:=mulFirstP
  let b:=unarySuccessor.comp ((((first unaryCode addTail1).comp addViewP).precompose
    (fun s:AddState=>s.val)).comp f)
  let g:=(addGraphP.precompose (fun s:AddState=>s.val)).comp f
  let out:=(addOutputP.precompose (fun s:AddState=>s.val)).comp f
  exact (packAddP.comp (b.pair (g.pair (binaryLhsP.pair (binaryRhsP.pair
    ((Procedure.constant _ Nat.bits 1).pair ((Procedure.constant _ refCode (0,false)).pair out))))))).result
      (by intro s;rfl)
noncomputable def mulBlastStateP : Procedure binaryStateCode mulStateCode mulBlastState :=
  mulIterationP.comp ((unaryPred.comp ((listUnaryLength refCode (0,false)).comp binaryLhsP)).pair initializeMulP)
noncomputable def swapBinaryP : Procedure binaryStateCode binaryStateCode swapBinary :=
  (swapAddP.precompose (fun s:BinaryState=>s.val)).result (by intro s;rfl)
noncomputable def mulStateP : Procedure binaryStateCode mulStateCode mulState := by
  let lk:=countKnownP.comp (binaryGraphP.pair binaryLhsP)
  let rk:=countKnownP.comp (binaryGraphP.pair binaryRhsP)
  exact (conditional (binaryLt.comp (lk.pair rk)) mulBlastStateP
    (mulBlastStateP.comp swapBinaryP)).congrFun (by intro s;unfold mulState;split <;> simp_all)
noncomputable def mulP : Procedure binaryStateCode (prodCode graphCode (listCode refCode))
    (fun s=>mul s.val.val.graph s.val.val.lhs s.val.val.rhs):=
  (((addGraphP.pair addOutputP).precompose (fun s:MulState=>s.val)).comp mulStateP).congrFun mulState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
