import OAI.Computability.WeisfeilerLeman.SparseSearch

namespace OAI

universe uA uB

namespace WLTime.SparseLookup
open TypedStack
def answer (w : ℕ) (q : List Bool) (l : List Entry) : List Bool :=
  if found q l=[] then List.replicate w false else found q l
def supplyZero (w : ℕ) : Code Reg Bool :=
  .branch (Code.nonempty 2) .skip (.pushList 2 (List.replicate w false))
def program (w : ℕ) : Code Reg Bool :=
  .seq (search w) (.seq (.transfer 3 0 false) (supplyZero w))
 theorem supplyZero_exec (w : ℕ) (log q out : List Bool) :
    ∃u ≤ 2*w+2,
      (supplyZero w).Exec (state log q out [] [] [] [] []) u
        (state log q (if out=[] then List.replicate w false else out) [] [] [] [] []) := by
  let s := state log q out [] [] [] [] []
  by_cases ho : out=[]
  · have hp := Code.pushList_exec (2 : Reg) (List.replicate w false) s
    have he := Code.Exec.branch_false (a:=Code.skip) (p:=Code.nonempty 2) (by simp [Code.nonempty,tops,s,state,ho]) hp
    refine ⟨1+(2*w+1),by omega,?_⟩
    have hh : Function.update s 2 (List.replicate w false++s 2)=state log q (if out=[] then List.replicate w false else out) [] [] [] [] [] := by
      funext i; fin_cases i <;> simp [s,state,ho]
    rw [hh] at he
    simpa only [supplyZero,s,List.length_replicate,Nat.add_comm] using he
  · have he := Code.Exec.branch_true (b:=Code.pushList 2 (List.replicate w false)) (p:=Code.nonempty 2)
      (by simp [Code.nonempty,tops,s,state,ho]) (Code.Exec.skip s)
    exact ⟨2,by omega,by simpa only [supplyZero,s,ite_eq_right ho] using he⟩
 theorem program_exec (q : List Bool) (l : List Entry) (hq : 0<q.length) (hw : WellFormed q.length l) :
    ∃u ≤ 60*(q.length+1)*(l.length+1),
      (program q.length).Exec (state (flatten l) q [] [] [] [] [] []) u
        (state (flatten l) q (answer q.length q l) [] [] [] [] []) := by
  obtain ⟨a,ha,he⟩ := search_exec q l [] hq hw
  simp only [List.append_nil] at he
  let mid := state (flatten (remaining q l)) q (found q l) (flatten (consumed q l)).reverse [] [] [] []
  have ht := Code.transfer_exec (3 : Reg) 0 (by decide) false mid
  have hs : Function.update (Function.update mid 3 []) 0 ((mid 3).reverse++mid 0)=
      state (flatten l) q (found q l) [] [] [] [] [] := by
    have hsplit : flatten (consumed q l)++flatten (remaining q l)=flatten l := by rw [←flatten_append,split_log]
    funext i; fin_cases i <;> simp [mid,state,hsplit]
  rw [hs] at ht
  obtain ⟨b,hb,hf⟩ := supplyZero_exec q.length (flatten l) q (found q l)
  refine ⟨_,?_,Code.Exec.seq he (Code.Exec.seq ht hf)⟩
  change a+(5*(flatten (consumed q l)).reverse.length+1+b) ≤ _
  rw [List.length_reverse]
  have hpre := consumed_length q l
  rw [flatten_length q.length l hw] at hpre
  nlinarith
 theorem program_size (w : ℕ) : (program w).controlSize ≤ 30*w+100 := by
  simp only [program,search,one,first,finish,supplyZero,Code.controlSize,Code.relabel_controlSize,
    SparseMatch.program_size,SparseTake.program_size,Code.copy,Code.transfer,Code.distribute,Code.clear,
    Code.pushList_size,List.length_replicate]
  omega
end WLTime.SparseLookup

namespace WLTime.WordMemory
open TypedStack
abbrev Log (w : ℕ) := List (Word w × Word w)
def read {w : ℕ} (q : Word w) : Log w → Word w
  | [] => ⟨0,by positivity⟩
  | e::l => if e.1=q then e.2 else read q l
def entries {w : ℕ} (l : Log w) : List SparseLookup.Entry :=
  l.map (fun e => (wordBits e.1,wordBits e.2))
 theorem entries_wellFormed {w : ℕ} (l : Log w) : SparseLookup.WellFormed w (entries l) := by
  intro e he
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
  simp [wordBits]
 theorem entries_length {w : ℕ} (l : Log w) : (entries l).length=l.length := by simp [entries]
 theorem word_zero (w : ℕ) : wordBits (⟨0,by positivity⟩ : Word w)=List.replicate w false := by
  simp [wordBits,List.ofFn_const]
 theorem answer_read {w : ℕ} (hw : 0<w) (q : Word w) (l : Log w) :
    SparseLookup.answer w (wordBits q) (entries l)=wordBits (read q l) := by
  induction l with
  | nil => simp [SparseLookup.answer,SparseLookup.found,entries,read,wordBits,List.ofFn_const]
  | cons e l ih =>
    by_cases he : e.1=q
    · have hne : wordBits e.2≠[] := by intro h; have hh := congrArg List.length h; simp [wordBits] at hh; omega
      simp [entries,SparseLookup.answer,SparseLookup.found,he,hne,read]
    · have hb : wordBits e.1≠wordBits q := fun h => he (BitWords.word_injective h)
      change SparseLookup.answer w (wordBits q) ((wordBits e.1,wordBits e.2)::entries l)=wordBits (if e.1=q then e.2 else read q l)
      rw [ite_eq_right he]
      unfold SparseLookup.answer
      rw [SparseLookup.found,ite_eq_right hb]
      exact ih
 theorem lookup_exec {w : ℕ} (hw : 0<w) (q : Word w) (l : Log w) :
    ∃u ≤ 60*(w+1)*(l.length+1),
      (SparseLookup.program w).Exec
        (SparseLookup.state (SparseLookup.flatten (entries l)) (wordBits q) [] [] [] [] [] []) u
        (SparseLookup.state (SparseLookup.flatten (entries l)) (wordBits q) (wordBits (read q l)) [] [] [] [] []) := by
  have hq : (wordBits q).length=w := by simp [wordBits]
  have he := SparseLookup.program_exec (wordBits q) (entries l) (by simpa [hq] using hw)
    (by rw [hq]; exact entries_wellFormed l)
  simpa only [hq,entries_length,answer_read hw] using he
 theorem read_prepend {w : ℕ} (l : Log w) (a v : Word w) :
    (fun q => read q ((a,v)::l))=Function.update (fun q => read q l) a v := by
  funext q
  by_cases h : a=q <;> simp [read,h,eq_comm]
end WLTime.WordMemory
namespace WLTime.SparseStore
open TypedStack
abbrev Reg := Fin 4
def state (log key value tmp : List Bool) : Stacks Reg Bool := ![log,key,value,tmp]
def program : Code Reg Bool := .seq (.copy 2 0 3 false) (.copy 1 0 3 false)
 theorem program_exec (log key value : List Bool) :
    program.Exec (state log key value []) (12*(key.length+value.length)+4)
      (state (key++value++log) key value []) := by
  let s := state log key value []
  let mid := state (value++log) key value []
  have h₁ : (Code.copy 2 0 3 false).Exec s (12*value.length+2) mid := by
    have h := Code.copy_exec (2 : Reg) 0 3 (by decide) (by decide) (by decide) false s rfl
    convert h using 1
    · rfl
    · funext i; fin_cases i <;> simp [s,mid,state]
  have h₂ : (Code.copy 1 0 3 false).Exec mid (12*key.length+2) (state (key++value++log) key value []) := by
    have h := Code.copy_exec (1 : Reg) 0 3 (by decide) (by decide) (by decide) false mid rfl
    convert h using 1
    · rfl
    · funext i; fin_cases i <;> simp [mid,state,List.append_assoc]
  have he := Code.Exec.seq h₁ h₂
  convert he using 1
  · rfl
  · omega
end WLTime.SparseStore

namespace WLTime.BitWords
 theorem value_sum (n : ℕ) (f : ℕ → Bool) :
    value (List.ofFn (fun i : Fin n => f i.val))=∑i∈Finset.range n, if f i then 2^i else 0 := by
  induction n generalizing f with
  | zero => simp [value]
  | succ n ih =>
    rw [List.ofFn_succ,value_cons]
    simp only [Fin.val_zero,Fin.val_succ]
    rw [ih (fun i => f (i+1))]
    rw [Finset.sum_range_succ']
    simp only [pow_succ]
    have hsum : (∑i∈Finset.range n,if f (i+1) then 2^i*2 else 0)=
        2*(∑i∈Finset.range n,if f (i+1) then 2^i else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      cases f (i+1) <;> simp [Nat.mul_comm]
    rw [hsum]
    cases f 0 <;> simp [Bool.toNat,Nat.add_comm]
end WLTime.BitWords
namespace WLTime.WordMemory
open TypedStack
def chunk (w : ℕ) (input : List Bool) (a : ℕ) : List Bool :=
  Code.readN false (input.drop (w*a)) w
 theorem chunk_length (w : ℕ) (input : List Bool) (a : ℕ) : (chunk w input a).length=w := by simp [chunk,Code.readN]
 theorem chunk_value (w : ℕ) (input : List Bool) (a : ℕ) :
    BitWords.value (chunk w input a)=
      ∑i∈Finset.range w,if input.getD (w*a+i) false then 2^i else 0 := by
  unfold chunk Code.readN
  rw [BitWords.value_sum w (fun i => (input.drop (w*a)).getD i false)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [List.getD_eq_getElem?_getD,List.getElem?_drop]
 theorem packed_bits (w : ℕ) (input : List Bool) (a : Word w) :
    wordBits (RAM.packedWord w input a)=chunk w input a.val := by
  have hv := BitWords.value_lt (chunk w input a.val)
  rw [chunk_length] at hv
  have he : (RAM.packedWord w input a).val=BitWords.value (chunk w input a.val) := by
    change _ % (2^w)=_
    rw [←chunk_value,Nat.mod_eq_of_lt hv]
  apply List.ext_getElem
  · simp [wordBits,chunk_length]
  · intro i hi hj
    simp only [wordBits,List.getElem_ofFn,he,BitWords.testBit_value]
    exact List.getD_eq_getElem _ _ hj
 theorem chunk_zero (w : ℕ) (input : List Bool) (a : ℕ) (ha : input.length  ≤  w*a) :
    chunk w input a=List.replicate w false := by
  simp [chunk,Code.readN,List.drop_eq_nil_of_le ha,List.ofFn_const]
end WLTime.WordMemory
namespace WLTime.WordMemory
def address (w a : ℕ) : Word w := ⟨a%(2^w),Nat.mod_lt _ (by positivity)⟩
 theorem address_val (w a : ℕ) (ha : a<2^w) : (address w a).val=a := Nat.mod_eq_of_lt ha
 theorem address_eq (w a : ℕ) (q : Word w) (ha : a<2^w) : address w a=q ↔ a=q.val := by
  rw [Fin.ext_iff,address_val w a ha]
def initialLog (w : ℕ) (input : List Bool) : ℕ → Log w
  | 0 => []
  | a+1 => (address w a,RAM.packedWord w input (address w a))::initialLog w input a
 theorem initialLog_length (w : ℕ) (input : List Bool) (a : ℕ) : (initialLog w input a).length=a := by
  induction a with
  | zero => rfl
  | succ a ih => simp [initialLog,ih]
 theorem read_initialLog (w : ℕ) (input : List Bool) (a : ℕ) (q : Word w) (ha : a ≤ 2^w) :
    read q (initialLog w input a)=if q.val<a then RAM.packedWord w input q else ⟨0,by positivity⟩ := by
  induction a with
  | zero => simp [initialLog,read]
  | succ a ih =>
    have hal : a<2^w := by omega
    have hh := ih (by omega)
    simp only [initialLog,read]
    by_cases he : address w a=q
    · rw [ite_eq_left he,he,ite_eq_left (by have := (address_eq w a q hal).mp he; omega)]
    · rw [ite_eq_right he,hh]
      have hne : a≠q.val := fun h => he ((address_eq w a q hal).mpr h)
      have heq : (q.val<a) ↔ (q.val<a+1) := by omega
      simp only [heq]
 theorem initialLog_correct (w : ℕ) (input : List Bool) (a : ℕ) (ha : a ≤ 2^w) (hl : input.length ≤ w*a) :
    (fun q => read q (initialLog w input a))=RAM.packedWord w input := by
  funext q
  rw [read_initialLog w input a q ha]
  split_ifs with hq
  · rfl
  · apply BitWords.word_injective
    rw [word_zero,packed_bits,chunk_zero w input q.val (hl.trans (Nat.mul_le_mul_left w (by omega)))]
 theorem number_of_chunks (w : ℕ) (hw : 0<w) (input : List Bool) :
    ∃n ≤ input.length, input.length ≤ w*n ∧ ∀ a < n, w*a < input.length := by
  have hex : ∃n,input.length ≤ w*n := ⟨input.length,by nlinarith⟩
  let n := Nat.find hex
  refine ⟨n,Nat.find_min' hex (by nlinarith),Nat.find_spec hex,?_⟩
  intro a ha
  exact Nat.lt_of_not_ge (Nat.find_min hex ha)
end WLTime.WordMemory
namespace WLTime.BitWords
 theorem eq_word {w : ℕ} (xs : List Bool) (a : Word w) (hl : xs.length=w) (hv : value xs=a.val) : xs=wordBits a := by
  apply List.ext_getElem
  · simpa [wordBits] using hl
  · intro i hi hj
    simp only [wordBits,List.getElem_ofFn,←hv,testBit_value]
    exact (List.getD_eq_getElem _ _ hi).symm
 theorem inc_address (w a : ℕ) : inc (wordBits (WordMemory.address w a))=wordBits (WordMemory.address w (a+1)) := by
  apply eq_word
  · simp [wordBits]
  · rw [inc_value,value_word]
    simp only [wordBits,List.length_ofFn,WordMemory.address]
    simp only [Nat.add_mod,Nat.mod_mod]
end WLTime.BitWords

namespace WLTime.RAMInput
open TypedStack WordMemory
abbrev Reg := Fin 6
def state (input log addr value temp scratch : List Bool) : Stacks Reg Bool :=
  ![input,log,addr,value,temp,scratch]
def storeMap : SparseStore.Reg → Reg := ![1,2,3,5]
theorem storeMap_inj : Function.Injective storeMap := by decide
noncomputable def body (w : ℕ) : Code Reg Bool :=
  .seq (.takeN 0 4 id false w) (.seq (.transfer 4 3 false)
    (.seq (SparseStore.program.relabel storeMap) (.seq (.clear 3) (.increment 2 5))))
def running (v : Tops Reg Bool) : Bool := Code.nonempty 0 v
noncomputable def loopCode (w : ℕ) : Code Reg Bool := .loop running (body w)
noncomputable def program (w : ℕ) : Code Reg Bool :=
  .seq (.pushList 2 (List.replicate w false)) (.seq (loopCode w) (.clear 2))
 theorem body_exec (w : ℕ) (input log addr : List Bool) (ha : addr.length=w) :
    ∃ u ≤ 50*(w+1), (body w).Exec (state input log addr [] [] []) u
      (state (input.drop w) (addr++Code.readN false input w++log) (BitWords.inc addr) [] [] []) := by
  let value := Code.readN false input w
  have hv : value.length=w := by simp [value,Code.readN]
  let s₀ := state input log addr [] [] []
  let s₁ := state (input.drop w) log addr [] value.reverse []
  let s₂ := state (input.drop w) log addr value [] []
  let s₃ := state (input.drop w) (addr++value++log) addr value [] []
  let s₄ := state (input.drop w) (addr++value++log) addr [] [] []
  have h₁ : (Code.takeN 0 4 id false w).Exec s₀ (4*w+1) s₁ := by
    have he := Code.takeN_exec (0 : Reg) 4 (by decide) id false w s₀
    convert he using 1
    funext i; fin_cases i <;> simp [s₀,s₁,state,value]
  have h₂ : (Code.transfer 4 3 false).Exec s₁ (5*w+1) s₂ := by
    have he := Code.transfer_exec (4 : Reg) 3 (by decide) false s₁
    convert he using 1
    · simp [s₁,state,hv]
    · funext i; fin_cases i <;> simp [s₁,s₂,state]
  have h₃ : (SparseStore.program.relabel storeMap).Exec s₂ (24*w+4) s₃ := by
    have he := SparseStore.program_exec log addr value
    have hc : 12*(addr.length+value.length)+4=24*w+4 := by rw [ha,hv]; omega
    rw [hc] at he
    apply Code.relabel_exec_of_maps storeMap storeMap_inj he
    · intro i; fin_cases i <;> simp [s₂,state,storeMap,SparseStore.state]
    · intro i; fin_cases i <;> simp [s₃,state,storeMap,SparseStore.state]
    · intro i hi; fin_cases i <;> simp_all [state,s₂,s₃,storeMap]

      exact False.elim (hi 0 rfl)
  have h₄ : (Code.clear 3).Exec s₃ (3*w+1) s₄ := by
    have he := Code.clear_exec (3 : Reg) s₃
    convert he using 1
    · simp [s₃,state,hv]
    · funext i; fin_cases i <;> simp [s₃,s₄,state]
  obtain ⟨u,hu,he⟩ := Code.increment_exec (2 : Reg) 5 (by decide) s₄ rfl
  have h₅ : (Code.increment 2 5).Exec s₄ u
      (state (input.drop w) (addr++value++log) (BitWords.inc addr) [] [] []) := by
    convert he using 1
    funext i; fin_cases i <;> simp [s₄,state]
  refine ⟨_,?_,Code.Exec.seq h₁ (Code.Exec.seq h₂ (Code.Exec.seq h₃ (Code.Exec.seq h₄ h₅)))⟩
  change u ≤ 10*addr.length+7 at hu
  rw [ha] at hu
  omega

def packedState (w : ℕ) (input : List Bool) (a : ℕ) : Stacks Reg Bool :=
  state (input.drop (w*a)) (SparseLookup.flatten (entries (initialLog w input a)))
    (wordBits (address w a)) [] [] []
 theorem body_packed (w : ℕ) (input : List Bool) (a : ℕ) (ha : a<2^w) :
    ∃ u ≤ 50*(w+1), (body w).Exec (packedState w input a) u (packedState w input (a+1)) := by
  obtain ⟨u,hu,he⟩ := body_exec w (input.drop (w*a))
    (SparseLookup.flatten (entries (initialLog w input a))) (wordBits (address w a)) (by simp [wordBits])
  refine ⟨u,hu,?_⟩
  convert he using 1 <;> try rfl
  unfold packedState
  rw [BitWords.inc_address]
  have hdrop : (input.drop (w*a)).drop w=input.drop (w*(a+1)) := by simp [List.drop_drop,Nat.mul_add,Nat.add_comm]
  rw [hdrop]
  rw [show initialLog w input (a+1)=(address w a,RAM.packedWord w input (address w a))::initialLog w input a from rfl]
  simp only [entries,SparseLookup.flatten,List.map_cons,List.flatMap_cons]
  rw [packed_bits,address_val w a ha]
  simp only [chunk,List.append_assoc]
 theorem loop_packed (w : ℕ) (input : List Bool) (n : ℕ) (hn : n ≤ 2^w)
    (hfinal : input.length ≤ w*n) (hmin : ∀ a < n, w*a < input.length) (t a : ℕ) (hat : a+t=n) :
    ∃ u ≤ 51*(w+1)*t+1, (loopCode w).Exec (packedState w input a) u (packedState w input n) := by
  induction t generalizing a with
  | zero =>
    have han : a=n := by omega
    subst a
    refine ⟨1,by omega,Code.Exec.loop_false ?_⟩
    simp [running,Code.nonempty,tops,packedState,state,List.drop_eq_nil_of_le hfinal]
  | succ t ih =>
    have han : a<n := by omega
    obtain ⟨u,hu,he⟩ := body_packed w input a (by omega)
    obtain ⟨v,hv,hh⟩ := ih (a+1) (by omega)
    have hp : running (tops (packedState w input a))=true := by
      simpa [running,Code.nonempty,tops,packedState,state,Option.isSome_iff_ne_none] using hmin a han
    refine ⟨_,?_,Code.Exec.loop_true hp he hh⟩
    nlinarith
 theorem program_exec (w : ℕ) (hw : 0<w) (input : List Bool) (hfit : input.length ≤ w*2^w) :
    ∃ n ≤ input.length, (fun q => read q (initialLog w input n))=RAM.packedWord w input ∧
      ∃ u ≤ 60*(w+1)*(input.length+1), (program w).Exec (state input [] [] [] [] []) u
        (state [] (SparseLookup.flatten (entries (initialLog w input n))) [] [] [] []) := by
  obtain ⟨n,hn,hfinal,hmin⟩ := number_of_chunks w hw input
  have hlimit : n ≤ 2^w := by
    by_contra h
    have ht := hmin (2^w) (by omega)
    omega
  refine ⟨n,hn,initialLog_correct w input n hlimit hfinal,?_⟩
  have hinit : (Code.pushList 2 (List.replicate w false)).Exec (state input [] [] [] [] []) (2*w+1) (packedState w input 0) := by
    have he := Code.pushList_exec (2 : Reg) (List.replicate w false) (state input [] [] [] [] [])
    convert he using 1
    · simp
    · funext i; fin_cases i <;> simp [packedState,state,initialLog,entries,SparseLookup.flatten,address,wordBits,List.ofFn_const]
  obtain ⟨u,hu,he⟩ := loop_packed w input n hlimit hfinal hmin n 0 (by omega)
  have hclear : (Code.clear 2).Exec (packedState w input n) (3*w+1)
      (state [] (SparseLookup.flatten (entries (initialLog w input n))) [] [] [] []) := by
    have hh := Code.clear_exec (2 : Reg) (packedState w input n)
    convert hh using 1
    · simp [packedState,state,wordBits]
    · funext i; fin_cases i <;> simp [packedState,state,List.drop_eq_nil_of_le hfinal]
  refine ⟨_,?_,Code.Exec.seq hinit (Code.Exec.seq he hclear)⟩
  nlinarith
 theorem body_size (w : ℕ) : (body w).controlSize ≤ 4*w+100 := by
  simp [body,Code.controlSize,Code.takeN_size,Code.relabel_controlSize,SparseStore.program,
    Code.copy,Code.transfer,Code.distribute,Code.clear,Code.increment,Code.carryCode,Code.raiseCode]
 theorem program_size (w : ℕ) : (program w).controlSize ≤ 6*w+110 := by
  have hb := body_size w
  simp only [program,loopCode,Code.controlSize,Code.pushList_size,List.length_replicate,Code.clear]
  omega
end WLTime.RAMInput

namespace WLTime.TypedStack.Code
variable {A : Type uA} {B : Type uB}
 theorem readN_all (z : A) (xs : List A) : readN z xs xs.length=xs := by
  apply List.ext_getElem
  · simp [readN]
  · intro i hi hj
    simp only [readN,List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ hj
 theorem readN_map (z : A) (f : A → B) (xs : List A) (n : ℕ) :
    readN (f z) (xs.map f) n=(readN z xs n).map f := by
  apply List.ext_getElem
  · simp [readN]
  · intro i hi hj
    simp only [readN,List.getElem_ofFn,List.getElem_map]
    exact List.getD_map _ _ _
end WLTime.TypedStack.Code
namespace WLTime.TMPort
open TypedStack
variable (M : TM)
abbrev Letter := Bool ⊕ TMTransducer.Letter M
abbrev Reg := Fin 3 ⊕ TMTransducer.Reg M
def port : Reg M := .inl 0
def temp : Reg M := .inl 1
def result : Reg M := .inl 2
def tapeIn : Reg M := .inr (.inr (TMTransducer.zeroTape M,true))
def inputSymbol : Letter M → Letter M
  | .inl b => .inr (.inl (M.symbol b))
  | _ => .inr (.inl (TMStack.blank M))
def outputSymbol : Letter M → Letter M
  | .inr (.inl a) => .inl (decide (a.val=2))
  | _ => .inl false
def unletter : Letter M → TMTransducer.Letter M
  | .inr a => a
  | _ => .inl (TMStack.blank M)
def inputState (xs : List Bool) : Stacks (Reg M) (Letter M) :=
  fun k => if k=port M then xs.map Sum.inl else []
def innerState (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) : Stacks (Reg M) (Letter M) :=
  Sum.elim (fun _ => []) (Code.listMap Sum.inr (TMTransducer.store M q s ds))
def load (n : ℕ) : Code (Reg M) (Letter M) :=
  .seq (.takeN (port M) (temp M) (inputSymbol M) (.inl false) n)
    (.seq (.transfer (temp M) (tapeIn M) (.inl false))
      (.push (.inr (TMTransducer.stateReg M)) (.inr (.inr (.inl ⟨0,by have := M.states_ge; omega⟩)))))
noncomputable def runCode : Code (Reg M) (Letter M) :=
  ((TMTransducer.runCode M).mapLetters Sum.inr (unletter M)).relabel Sum.inr
noncomputable def rewindCode : Code (Reg M) (Letter M) :=
  ((TMTransducer.rewindCode M).mapLetters Sum.inr (unletter M)).relabel Sum.inr
def extract (n : ℕ) : Code (Reg M) (Letter M) :=
  .seq (.takeN (tapeIn M) (result M) (outputSymbol M) (.inr (.inl (TMStack.blank M))) n)
    (.transfer (result M) (port M) (.inl false))
 theorem load_exec (xs : List Bool) : (load M xs.length).Exec (inputState M xs) (9*xs.length+4)
    (innerState M (M.initial xs).state (TMStack.initialTapes M xs) []) := by
  have he := Code.takeN_exec (port M) (temp M) (by simp [port,temp]) (inputSymbol M) (.inl false) xs.length (inputState M xs)
  have hr : Code.readN (.inl false) (inputState M xs (port M)) xs.length=xs.map Sum.inl := by
    rw [inputState,ite_eq_left rfl]
    rw [←List.length_map (f:=Sum.inl) (as:=xs)]
    exact Code.readN_all _ _
  have hm : (xs.map Sum.inl).map (inputSymbol M)=(xs.map M.symbol).map (fun a => Sum.inr (Sum.inl a)) := by
    simp only [List.map_map]; rfl
  rw [hr,hm] at he
  let mid := Function.update (Function.update (inputState M xs) (port M) []) (temp M)
    (((xs.map M.symbol).map (fun a => Sum.inr (Sum.inl a))).reverse)
  have he' : (Code.takeN (port M) (temp M) (inputSymbol M) (.inl false) xs.length).Exec (inputState M xs) (4*xs.length+1) mid := by
    simpa [mid,inputState,port,temp,←List.map_drop] using he
  have ht := Code.transfer_exec (temp M) (tapeIn M) (by simp [temp,tapeIn]) (.inl false) mid
  let after := Function.update (Function.update mid (temp M) []) (tapeIn M) ((mid (temp M)).reverse++mid (tapeIn M))
  have hp := Code.Exec.push after (.inr (TMTransducer.stateReg M)) (.inr (.inr (.inl (M.initial xs).state)))
  have hex := Code.Exec.seq he' (Code.Exec.seq ht hp)
  have hout : Function.update after (.inr (TMTransducer.stateReg M))
      (.inr (.inr (.inl (M.initial xs).state))::after (.inr (TMTransducer.stateReg M)))=
      innerState M (M.initial xs).state (TMStack.initialTapes M xs) [] := by
    funext k
    cases k with
    | inl i => fin_cases i <;> simp [after,mid,inputState,innerState,port,temp,tapeIn,TMTransducer.stateReg]
    | inr k => cases k with
      | inl i => fin_cases i <;> simp [after,mid,inputState,innerState,port,temp,tapeIn,TMTransducer.stateReg,TMTransducer.store,Code.listMap]
      | inr k =>
        rcases k with ⟨a,b⟩
        by_cases ha : a=TMTransducer.zeroTape M
        · subst a
          cases b <;> simp [after,mid,inputState,innerState,port,temp,tapeIn,TMTransducer.stateReg,TMTransducer.store,Code.listMap,TMStack.store,TMStack.initialTapes,TMTransducer.zeroTape,List.map_map,Function.comp_def]
        · have hv : a.val≠0 := fun h => ha (Fin.ext h)
          cases b <;> simp [after,mid,inputState,innerState,port,temp,tapeIn,TMTransducer.stateReg,TMTransducer.store,Code.listMap,TMStack.store,TMStack.initialTapes,hv,TMTransducer.zeroTape,Function.update_apply]
          ; simp_all [Fin.ext_iff]
  rw [hout] at hex
  convert hex using 1
  · rfl
  · simp [mid]; omega
 theorem run_exec (input output : List Bool) (ho : M.outputs input output) :
    ∃u  ≤  TMTransducer.stepFactor M*M.time input+1,∃s ds,
      (runCode M).Exec (innerState M (M.initial input).state (TMStack.initialTapes M input) []) u
        (innerState M (M.run input (M.time input)).state s ds) ∧
      TMStack.Relative M (M.run input (M.time input)) s ∧ ds.length ≤  M.time input ∧
      (M.run input (M.time input)).head (TMTransducer.zeroTape M)=(ds.map Move.displacement).sum := by
  obtain ⟨u,hu,s,ds,he,hr,hlen,hh⟩ := TMTransducer.run_exec M (M.initial input)
    (TMStack.initialTapes M input) [] (M.time input) (TMStack.initial_relative M input)
    (M.time_halted input ho.1)
  refine ⟨u,hu,s,ds,?_,hr,by simpa using hlen,by simpa only [TM.initial,List.map_nil,List.sum_nil,sub_zero,zero_add,TM.run,TMTransducer.zeroTape] using hh⟩
  exact Code.relabel_inr_exec (Code.mapLetters_exec Sum.inr (unletter M) (by intro a; rfl) he) (fun _ : Fin 3 => [])
 theorem rewind_exec (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) :
    ∃u  ≤  TMTransducer.rewindFactor M*ds.length+1,(rewindCode M).Exec (innerState M q s ds) u
      (innerState M q (TMTransducer.rewindTapes M s ds) []) := by
  obtain ⟨u,hu,he⟩ := TMTransducer.rewind_exec M q s ds
  exact ⟨u,hu,Code.relabel_inr_exec (Code.mapLetters_exec Sum.inr (unletter M) (by intro a; rfl) he) (fun _ : Fin 3 => [])⟩
end WLTime.TMPort

end OAI
