import OAI.Computability.WeisfeilerLeman.SparseStore

namespace OAI

universe uA

namespace WLTime.TMPort
open TypedStack
variable (M : TM)
 theorem output_symbol (b : Bool) : outputSymbol M (.inr (.inl (M.symbol b)))=.inl b := by
  cases b <;> simp [outputSymbol,TM.symbol]
 theorem extract_exec (s : Stacks (Reg M) (Letter M)) (ys : List Bool)
    (hp : s (port M)=[]) (hr : s (result M)=[])
    (hout : Code.readN (.inr (.inl (TMStack.blank M))) (s (tapeIn M)) ys.length=
      ys.map (fun b => .inr (.inl (M.symbol b)))) :
    (extract M ys.length).Exec s (9*ys.length+2)
      (Function.update (Function.update s (tapeIn M) ((s (tapeIn M)).drop ys.length)) (port M) (ys.map Sum.inl)) := by
  have he := Code.takeN_exec (tapeIn M) (result M) (by simp [tapeIn,result]) (outputSymbol M)
    (.inr (.inl (TMStack.blank M))) ys.length s
  have hm : (ys.map (fun b => Sum.inr (Sum.inl (M.symbol b)))).map (outputSymbol M)=ys.map Sum.inl := by
    simp only [List.map_map]
    congr 1
    funext b
    exact output_symbol M b
  rw [hout,hm,hr,List.append_nil] at he
  let mid := Function.update (Function.update s (tapeIn M) ((s (tapeIn M)).drop ys.length)) (result M) (ys.map Sum.inl).reverse
  have ht := Code.transfer_exec (result M) (port M) (by simp [result,port]) (.inl false) mid
  have hh := Code.Exec.seq he ht
  have hf : Function.update (Function.update mid (result M) []) (port M) ((mid (result M)).reverse++mid (port M))=
      Function.update (Function.update s (tapeIn M) ((s (tapeIn M)).drop ys.length)) (port M) (ys.map Sum.inl) := by
    funext k
    by_cases hkp : k=port M
    · subst k; simp [mid,port,result,tapeIn,show s (.inl 0)=[] from hp]
    · by_cases hkr : k=result M
      · subst k; simp [mid,port,result,tapeIn,show s (.inl 2)=[] from hr]
      · simp [mid,hkp,hkr]
  rw [hf] at hh
  convert hh using 1
  · rfl
  · simp [mid]; omega
 theorem extract_inner (input output : List Bool) (ho : M.outputs input output)
    (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move)
    (hr : TMStack.Relative M (M.run input (M.time input)) s)
    (hh : (M.run input (M.time input)).head (TMTransducer.zeroTape M)=(ds.map Move.displacement).sum) :
    Code.readN (.inr (.inl (TMStack.blank M)))
      (innerState M (M.run input (M.time input)).state (TMTransducer.rewindTapes M s ds) [] (tapeIn M)) output.length=
      output.map (fun b => .inr (.inl (M.symbol b))) := by
  have h := TMTransducer.output_prefix M input output ho s ds hr hh
  change Code.readN _ (((TMTransducer.rewindTapes M s ds (TMTransducer.zeroTape M)).right.map Sum.inl).map Sum.inr) _=_
  rw [Code.readN_map,Code.readN_map,h]
  simp only [List.map_map]
  rfl
end WLTime.TMPort
namespace WLTime.TMPort
open TypedStack
open scoped Classical
variable (M : TM)
noncomputable def privateRegs : List (Reg M) := (Finset.univ : Finset (TMTransducer.Reg M)).toList.map Sum.inr
noncomputable def program (n o : ℕ) : Code (Reg M) (Letter M) :=
  .seq (load M n) (.seq (runCode M) (.seq (rewindCode M) (.seq (extract M o) (.clearList (privateRegs M)))))
noncomputable def factor : ℕ := 50+4*(TMTransducer.stepFactor M+TMTransducer.rewindFactor M)+Fintype.card (TMTransducer.Reg M)
 theorem input_mass (xs : List Bool) : Code.mass (inputState M xs)=xs.length := by
  unfold Code.mass inputState
  rw [Finset.sum_eq_single (port M)]
  · simp
  · intro b hb hne; simp [hne]
  · simp
 theorem private_nodup : (privateRegs M).Nodup := by
  exact (Finset.nodup_toList (Finset.univ : Finset (TMTransducer.Reg M))).map Sum.inr_injective
 theorem private_mem (k : Reg M) : k∈privateRegs M ↔ ∃r,k=Sum.inr r := by
  simp [privateRegs,eq_comm]
 theorem cleanup (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) (ys : List Bool) :
    Code.cleared (privateRegs M)
      (Function.update (Function.update (innerState M q s ds) (tapeIn M)
        ((innerState M q s ds (tapeIn M)).drop ys.length)) (port M) (ys.map Sum.inl))=inputState M ys := by
  funext k
  cases k with
  | inl i =>
    have hn : (Sum.inl i : Reg M)∉privateRegs M := by rw [private_mem]; simp
    simp only [Code.cleared,ite_eq_right hn,inputState]
    by_cases h : (Sum.inl i : Reg M)=port M
    · rw [ite_eq_left h,h,Function.update_self]
    · rw [ite_eq_right h,Function.update_of_ne h,Function.update_of_ne (show (Sum.inl i : Reg M)≠tapeIn M from Sum.inl_ne_inr)]
      rfl
  | inr r =>
    have hn : (Sum.inr r : Reg M)∈privateRegs M := by rw [private_mem]; exact ⟨r,rfl⟩
    simp only [Code.cleared,ite_eq_left hn,inputState,port,Sum.inr_ne_inl,ite_false]
 theorem program_exec (input output : List Bool) (ho : M.outputs input output) :
    ∃u ≤ factor M*(input.length+M.time input+output.length+1),
      (program M input.length output.length).Exec (inputState M input) u (inputState M output) := by
  have hl := load_exec M input
  obtain ⟨a,ha,s,ds,he,hr,hd,hh⟩ := run_exec M input output ho
  obtain ⟨b,hb,hf⟩ := rewind_exec M (M.run input (M.time input)).state s ds
  let z := innerState M (M.run input (M.time input)).state (TMTransducer.rewindTapes M s ds) []
  have hg := extract_exec M z output rfl rfl (extract_inner M input output ho s ds hr hh)
  let out := Function.update (Function.update z (tapeIn M) ((z (tapeIn M)).drop output.length)) (port M) (output.map Sum.inl)
  have hpre := Code.Exec.seq hl (Code.Exec.seq he (Code.Exec.seq hf hg))
  have hmass := Code.mass_exec hpre
  rw [input_mass] at hmass
  have hs := Code.clearList_cost (privateRegs M) out (private_nodup M)
  have hc := Code.clearList_exec (privateRegs M) out (private_nodup M)
  rw [cleanup] at hc
  have hfull := Code.Exec.seq hl (Code.Exec.seq he (Code.Exec.seq hf (Code.Exec.seq hg hc)))
  refine ⟨_,?_,hfull⟩
  have hlen : (privateRegs M).length=Fintype.card (TMTransducer.Reg M) := by simp [privateRegs]
  rw [hlen]
  have hbb := (Nat.mul_le_mul_left (TMTransducer.rewindFactor M) hd)
  have hbound : a+b ≤ (TMTransducer.stepFactor M+TMTransducer.rewindFactor M)*M.time input+2 := by nlinarith only [ha,hb,hbb]
  change Code.mass out ≤ input.length+(9*input.length+4+(a+(b+(9*output.length+2)))) at hmass
  dsimp only [factor]
  nlinarith only [hmass,hs,hbound,Nat.zero_le ((TMTransducer.stepFactor M+TMTransducer.rewindFactor M)*(input.length+output.length+1)),
    Nat.zero_le (Fintype.card (TMTransducer.Reg M)*(input.length+M.time input+output.length))]
 theorem size_load (n : ℕ) : (load M n).controlSize=4*n+8 := by
  simp only [load,Code.controlSize,Code.takeN_size,Code.transfer]
 theorem size_extract (n : ℕ) : (extract M n).controlSize=4*n+6 := by
  simp only [extract,Code.controlSize,Code.takeN_size,Code.transfer]
noncomputable def sizeFactor : ℕ := 14+(runCode M).controlSize+(rewindCode M).controlSize+(Code.clearList (privateRegs M) : Code (Reg M) (Letter M)).controlSize
 theorem program_size (n o : ℕ) : (program M n o).controlSize ≤ sizeFactor M*(n+o+1) := by
  simp only [program,Code.controlSize,size_load,size_extract,sizeFactor]
  nlinarith
end WLTime.TMPort

namespace WLTime.TypedStack.Code
variable {A : Type uA}
theorem readN_prefix (z : A) (xs tail : List A) : readN z (xs++tail) xs.length=xs := by
  apply List.ext_getElem
  · simp [readN]
  · intro i hi hj
    simp only [readN,List.getElem_ofFn,List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hj,List.getElem?_eq_getElem hj]
    rfl
end WLTime.TypedStack.Code
namespace WLTime.RAMSlices
open TypedStack
abbrev Reg := Fin 4
def state (file value pre tmp : List Bool) : Stacks Reg Bool := ![file,value,pre,tmp]
def read (offset len : ℕ) : Code Reg Bool :=
  .seq (.copy 0 2 3 false) (.seq (.takeN 2 3 id false offset) (.seq (.clear 3)
    (.seq (.takeN 2 3 id false len) (.seq (.clear 2) (.transfer 3 1 false)))))
def write (offset len : ℕ) : Code Reg Bool :=
  .seq (.takeN 0 2 id false offset) (.seq (.takeN 0 3 id false len) (.seq (.clear 3)
    (.seq (.moveList 1 0 3 false) (.transfer 2 0 false))))
 theorem read_exec (pre value post : List Bool) :
    ∃ u ≤ 60*((pre++value++post).length+1),
      (read pre.length value.length).Exec (state (pre++value++post) [] [] []) u
        (state (pre++value++post) value [] []) := by
  let file := pre++value++post
  let s₀ := state file [] [] []
  let s₁ := state file [] file []
  let s₂ := state file [] (value++post) pre.reverse
  let s₃ := state file [] (value++post) []
  let s₄ := state file [] post value.reverse
  let s₅ := state file [] [] value.reverse
  have h₁ : (Code.copy 0 2 3 false).Exec s₀ (12*file.length+2) s₁ := by
    have he := Code.copy_exec (0 : Reg) 2 3 (by decide) (by decide) (by decide) false s₀ rfl
    convert he using 1 <;> try rfl
    funext i; fin_cases i <;> simp [s₀,s₁,state]
  have h₂ : (Code.takeN 2 3 id false pre.length).Exec s₁ (4*pre.length+1) s₂ := by
    have he := Code.takeN_exec (2 : Reg) 3 (by decide) id false pre.length s₁
    convert he using 1
    funext i; fin_cases i <;> simp [s₁,s₂,state,file,List.append_assoc,Code.readN_prefix]
  have h₃ : (Code.clear 3).Exec s₂ (3*pre.length+1) s₃ := by
    have he := Code.clear_exec (3 : Reg) s₂
    convert he using 1
    · simp [s₂,state]
    · funext i; fin_cases i <;> simp [s₂,s₃,state]
  have h₄ : (Code.takeN 2 3 id false value.length).Exec s₃ (4*value.length+1) s₄ := by
    have he := Code.takeN_exec (2 : Reg) 3 (by decide) id false value.length s₃
    convert he using 1
    funext i; fin_cases i <;> simp [s₃,s₄,state,Code.readN_prefix]
  have h₅ : (Code.clear 2).Exec s₄ (3*post.length+1) s₅ := by
    have he := Code.clear_exec (2 : Reg) s₄
    convert he using 1
    · rfl
    · funext i; fin_cases i <;> simp [s₄,s₅,state]
  have h₆ : (Code.transfer 3 1 false).Exec s₅ (5*value.length+1) (state file value [] []) := by
    have he := Code.transfer_exec (3 : Reg) 1 (by decide) false s₅
    convert he using 1
    · simp [s₅,state]
    · funext i; fin_cases i <;> simp [s₅,state]
  refine ⟨_,?_,Code.Exec.seq h₁ (Code.Exec.seq h₂ (Code.Exec.seq h₃ (Code.Exec.seq h₄ (Code.Exec.seq h₅ h₆))))⟩
  simp only [file,List.length_append]
  omega
 theorem write_exec (pre old post value : List Bool) (hlen : value.length=old.length) :
    ∃ u ≤ 30*((pre++old++post).length+1),
      (write pre.length old.length).Exec (state (pre++old++post) value [] []) u
        (state (pre++value++post) [] [] []) := by
  let s₀ := state (pre++old++post) value [] []
  let s₁ := state (old++post) value pre.reverse []
  let s₂ := state post value pre.reverse old.reverse
  let s₃ := state post value pre.reverse []
  let s₄ := state (value++post) [] pre.reverse []
  have h₁ : (Code.takeN 0 2 id false pre.length).Exec s₀ (4*pre.length+1) s₁ := by
    have he := Code.takeN_exec (0 : Reg) 2 (by decide) id false pre.length s₀
    convert he using 1
    funext i; fin_cases i <;> simp [s₀,s₁,state,List.append_assoc,Code.readN_prefix]
  have h₂ : (Code.takeN 0 3 id false old.length).Exec s₁ (4*old.length+1) s₂ := by
    have he := Code.takeN_exec (0 : Reg) 3 (by decide) id false old.length s₁
    convert he using 1
    funext i; fin_cases i <;> simp [s₁,s₂,state,Code.readN_prefix]
  have h₃ : (Code.clear 3).Exec s₂ (3*old.length+1) s₃ := by
    have he := Code.clear_exec (3 : Reg) s₂
    convert he using 1
    · simp [s₂,state]
    · funext i; fin_cases i <;> simp [s₂,s₃,state]
  have h₄ : (Code.moveList 1 0 3 false).Exec s₃ (10*value.length+2) s₄ := by
    have he := Code.moveList_exec (1 : Reg) 0 3 (by decide) (by decide) (by decide) false s₃ rfl
    convert he using 1 <;> try rfl
    funext i; fin_cases i <;> simp [s₃,s₄,state]
  have h₅ : (Code.transfer 2 0 false).Exec s₄ (5*pre.length+1) (state (pre++value++post) [] [] []) := by
    have he := Code.transfer_exec (2 : Reg) 0 (by decide) false s₄
    convert he using 1
    · simp [s₄,state]
    · funext i; fin_cases i <;> simp [s₄,state,List.append_assoc]
  refine ⟨_,?_,Code.Exec.seq h₁ (Code.Exec.seq h₂ (Code.Exec.seq h₃ (Code.Exec.seq h₄ h₅)))⟩
  simp only [List.length_append]
  omega
 theorem read_size (offset len : ℕ) : (read offset len).controlSize ≤ 4*(offset+len)+40 := by
  simp [read,Code.controlSize,Code.takeN_size,Code.copy,Code.transfer,Code.distribute,Code.clear]
  omega
 theorem write_size (offset len : ℕ) : (write offset len).controlSize ≤ 4*(offset+len)+30 := by
  simp [write,Code.controlSize,Code.takeN_size,Code.moveList,Code.transfer,Code.clear]
  omega
end WLTime.RAMSlices

namespace WLTime.RegisterFile
 theorem flatten_length {A : Type uA} (w : ℕ) (xs : List (List A)) (hx : ∀ x ∈ xs,x.length=w) :
    xs.flatten.length=w*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := hx x (by simp)
    have ht := ih (fun a ha => hx a (by simp [ha]))
    simp only [List.flatten_cons,List.length_append,List.length_cons,hh,ht]
    ring
 theorem length {R w : ℕ} (a : Fin R → Word w) : (registerBits a).length=R*w := by
  unfold registerBits
  rw [flatten_length w _ (by intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; simp [wordBits])]
  simp [Nat.mul_comm]
 theorem zero (R w : ℕ) : registerBits (fun _ : Fin R => (⟨0,by positivity⟩ : Word w))=List.replicate (R*w) false := by
  simp [registerBits,wordBits,List.ofFn_const]
 theorem update_list {R w : ℕ} (a : Fin R → Word w) (i : Fin R) (v : Word w) :
    (List.ofFn (fun j => wordBits (Function.update a i v j)))=
      (List.ofFn (fun j => wordBits (a j))).set i.val (wordBits v) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_ofFn,List.getElem_set]
    by_cases h : j=i.val
    · subst j
      simp
    · have hh : (⟨j,by simpa using hj⟩ : Fin R)≠i := by simpa [Fin.ext_iff] using h
      simp [Ne.symm h,hh]
 theorem split {R w : ℕ} (a : Fin R → Word w) (i : Fin R) :
    ∃ pre post : List Bool, pre.length=w*i.val ∧
      registerBits a=pre++wordBits (a i)++post ∧
      ∀ v : Word w,registerBits (Function.update a i v)=pre++wordBits v++post := by
  let xs := List.ofFn (fun j => wordBits (a j))
  have hi : i.val<xs.length := by simp [xs]
  have hw : ∀x∈xs,x.length=w := by
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    simp [wordBits]
  have hs : xs=xs.take i.val++xs[i.val]::xs.drop (i.val+1) := by
    have h := List.take_append_drop i.val xs
    rw [List.drop_eq_getElem_cons hi] at h
    exact h.symm
  refine ⟨(xs.take i.val).flatten,(xs.drop (i.val+1)).flatten,?_,?_,?_⟩
  · rw [flatten_length w _ (fun x hx => hw x (List.mem_of_mem_take hx)),List.length_take]
    rw [Nat.min_eq_left (Nat.le_of_lt hi)]
  · change xs.flatten=_
    conv_lhs => rw [hs]
    simp only [List.flatten_append,List.flatten_cons,List.append_assoc]
    simp only [xs,List.getElem_ofFn]
  · intro v
    unfold registerBits
    rw [update_list,List.set_eq_take_append_cons_drop,ite_eq_left (by simp)]
    simp only [List.flatten_append,List.flatten_cons,List.append_assoc]
    rfl
end WLTime.RegisterFile

namespace WLTime.RAMMemory
open TypedStack WordMemory
abbrev Reg := Fin 12
def state (file log key value : List Bool) : Stacks Reg Bool :=
  ![file,log,key,value,[],[],[],[],[],[],[],[]]
def keyMap : RAMSlices.Reg → Reg := ![0,2,4,5]
def valueMap : RAMSlices.Reg → Reg := ![0,3,4,5]
def lookupMap : SparseLookup.Reg → Reg := ![1,2,3,6,7,8,9,10]
def storeMap : SparseStore.Reg → Reg := ![1,2,3,5]
theorem keyMap_inj : Function.Injective keyMap := by decide
theorem valueMap_inj : Function.Injective valueMap := by decide
theorem lookupMap_inj : Function.Injective lookupMap := by decide
theorem storeMap_inj : Function.Injective storeMap := by decide
noncomputable def readKey (w i : ℕ) : Code Reg Bool := (RAMSlices.read (w*i) w).relabel keyMap
noncomputable def readValue (w i : ℕ) : Code Reg Bool := (RAMSlices.read (w*i) w).relabel valueMap
noncomputable def writeValue (w i : ℕ) : Code Reg Bool := (RAMSlices.write (w*i) w).relabel valueMap
noncomputable def lookup (w : ℕ) : Code Reg Bool := (SparseLookup.program w).relabel lookupMap
noncomputable def store : Code Reg Bool := SparseStore.program.relabel storeMap
noncomputable def load (w dest addr : ℕ) : Code Reg Bool :=
  .seq (readKey w addr) (.seq (lookup w) (.seq (writeValue w dest) (.clear 2)))
noncomputable def save (w addr src : ℕ) : Code Reg Bool :=
  .seq (readKey w addr) (.seq (readValue w src) (.seq store (.seq (.clear 2) (.clear 3))))
 theorem readKey_exec {R w : ℕ} (a : Fin R → Word w) (i : Fin R) (log value : List Bool) :
    ∃ u ≤ 60*(R*w+1), (readKey w i.val).Exec (state (registerBits a) log [] value) u
      (state (registerBits a) log (wordBits (a i)) value) := by
  obtain ⟨pre,post,hpre,hs,_⟩ := RegisterFile.split a i
  obtain ⟨u,hu,he⟩ := RAMSlices.read_exec pre (wordBits (a i)) post
  rw [←hs,RegisterFile.length] at hu
  rw [hpre,show (wordBits (a i)).length=w from by simp [wordBits]] at he
  refine ⟨u,hu,?_⟩
  apply Code.relabel_exec_of_maps keyMap keyMap_inj he
  · intro k; fin_cases k <;> simp [state,keyMap,RAMSlices.state,hs]
  · intro k; fin_cases k <;> simp [state,keyMap,RAMSlices.state,hs]
  · intro k hk; fin_cases k <;> simp_all [state,keyMap,Fin.forall_fin_succ]
 theorem readValue_exec {R w : ℕ} (a : Fin R → Word w) (i : Fin R) (log key : List Bool) :
    ∃ u ≤ 60*(R*w+1), (readValue w i.val).Exec (state (registerBits a) log key []) u
      (state (registerBits a) log key (wordBits (a i))) := by
  obtain ⟨pre,post,hpre,hs,_⟩ := RegisterFile.split a i
  obtain ⟨u,hu,he⟩ := RAMSlices.read_exec pre (wordBits (a i)) post
  rw [←hs,RegisterFile.length] at hu
  rw [hpre,show (wordBits (a i)).length=w from by simp [wordBits]] at he
  refine ⟨u,hu,?_⟩
  apply Code.relabel_exec_of_maps valueMap valueMap_inj he
  · intro k; fin_cases k <;> simp [state,valueMap,RAMSlices.state,hs]
  · intro k; fin_cases k <;> simp [state,valueMap,RAMSlices.state,hs]
  · intro k hk; fin_cases k <;> simp_all [state,valueMap,Fin.forall_fin_succ]
 theorem writeValue_exec {R w : ℕ} (a : Fin R → Word w) (i : Fin R) (v : Word w) (log key : List Bool) :
    ∃ u ≤ 30*(R*w+1), (writeValue w i.val).Exec (state (registerBits a) log key (wordBits v)) u
      (state (registerBits (Function.update a i v)) log key []) := by
  obtain ⟨pre,post,hpre,hs,ht⟩ := RegisterFile.split a i
  obtain ⟨u,hu,he⟩ := RAMSlices.write_exec pre (wordBits (a i)) post (wordBits v) (by simp [wordBits])
  rw [←hs,RegisterFile.length] at hu
  rw [hpre,show (wordBits (a i)).length=w from by simp [wordBits]] at he
  refine ⟨u,hu,?_⟩
  apply Code.relabel_exec_of_maps valueMap valueMap_inj he
  · intro k; fin_cases k <;> simp [state,valueMap,RAMSlices.state,hs]
  · intro k; fin_cases k <;> simp [state,valueMap,RAMSlices.state,ht]
  · intro k hk; fin_cases k <;> simp_all [state,valueMap,Fin.forall_fin_succ]
 theorem lookup_exec {w : ℕ} (hw : 0<w) (q : Word w) (l : Log w) (file : List Bool) :
    ∃ u ≤ 60*(w+1)*(l.length+1), (lookup w).Exec (state file (SparseLookup.flatten (entries l)) (wordBits q) []) u
      (state file (SparseLookup.flatten (entries l)) (wordBits q) (wordBits (read q l))) := by
  obtain ⟨u,hu,he⟩ := WordMemory.lookup_exec hw q l
  refine ⟨u,hu,?_⟩
  apply Code.relabel_exec_of_maps lookupMap lookupMap_inj he
  · intro k; fin_cases k <;> simp [state,lookupMap,SparseLookup.state]
  · intro k; fin_cases k <;> simp [state,lookupMap,SparseLookup.state]
  · intro k hk; fin_cases k <;> simp_all [state,lookupMap,Fin.forall_fin_succ]
 theorem store_exec {w : ℕ} (q v : Word w) (l : Log w) (file : List Bool) :
    store.Exec (state file (SparseLookup.flatten (entries l)) (wordBits q) (wordBits v)) (24*w+4)
      (state file (SparseLookup.flatten (entries ((q,v)::l))) (wordBits q) (wordBits v)) := by
  have he := SparseStore.program_exec (SparseLookup.flatten (entries l)) (wordBits q) (wordBits v)
  have hc : 12*((wordBits q).length+(wordBits v).length)+4=24*w+4 := by simp [wordBits]; omega
  rw [hc] at he
  apply Code.relabel_exec_of_maps storeMap storeMap_inj he
  · intro k; fin_cases k <;> simp [state,storeMap,SparseStore.state]
  · intro k; fin_cases k <;> simp [state,storeMap,SparseStore.state,entries,SparseLookup.flatten,List.append_assoc]
  · intro k hk; fin_cases k <;> simp_all [state,storeMap,Fin.forall_fin_succ]
 theorem clear_key (file log key value : List Bool) :
    (Code.clear 2).Exec (state file log key value) (3*key.length+1) (state file log [] value) := by
  have he := Code.clear_exec (2 : Reg) (state file log key value)
  convert he using 1 <;> try rfl
  funext k; fin_cases k <;> simp [state]
 theorem clear_value (file log key value : List Bool) :
    (Code.clear 3).Exec (state file log key value) (3*value.length+1) (state file log key []) := by
  have he := Code.clear_exec (3 : Reg) (state file log key value)
  convert he using 1 <;> try rfl
  funext k; fin_cases k <;> simp [state]
 def cost (R w L : ℕ) := 500*(R+1)*(w+1)*(L+1)
 theorem cost_arith (R w L : ℕ) :
    90*(R*w+1)+60*(w+1)*(L+1)+(3*w+1) ≤ cost R w L ∧
    120*(R*w+1)+(24*w+4)+2*(3*w+1) ≤ cost R w 0 := by
  have h₁ : R*w+1 ≤ (R+1)*(w+1) := by nlinarith
  have h₂ : (R+1)*(w+1) ≤ (R+1)*(w+1)*(L+1) := Nat.le_mul_of_pos_right _ (by omega)
  have h₃ : (w+1)*(L+1) ≤ (R+1)*(w+1)*(L+1) := Nat.mul_le_mul_right _ (by nlinarith)
  have h₄ : w+1 ≤ (R+1)*(w+1) := by nlinarith
  unfold cost
  constructor <;> nlinarith only [h₁,h₂,h₃,h₄]
 theorem load_exec {R w : ℕ} (hw : 0<w) (a : Fin R → Word w) (l : Log w) (dest addr : Fin R) :
    ∃ u ≤ cost R w l.length, (load w dest.val addr.val).Exec (state (registerBits a) (SparseLookup.flatten (entries l)) [] []) u
      (state (registerBits (Function.update a dest (read (a addr) l))) (SparseLookup.flatten (entries l)) [] []) := by
  obtain ⟨x,hx,he⟩ := readKey_exec a addr (SparseLookup.flatten (entries l)) []
  obtain ⟨y,hy,hf⟩ := lookup_exec hw (a addr) l (registerBits a)
  obtain ⟨z,hz,hg⟩ := writeValue_exec a dest (read (a addr) l) (SparseLookup.flatten (entries l)) (wordBits (a addr))
  have hh := clear_key (registerBits (Function.update a dest (read (a addr) l))) (SparseLookup.flatten (entries l)) (wordBits (a addr)) []
  have hc := (cost_arith R w l.length).1
  refine ⟨_,?_,Code.Exec.seq he (Code.Exec.seq hf (Code.Exec.seq hg hh))⟩
  simp only [wordBits,List.length_ofFn]
  omega
 theorem save_exec {R w : ℕ} (a : Fin R → Word w) (l : Log w) (addr src : Fin R) :
    ∃ u ≤ cost R w 0, (save w addr.val src.val).Exec (state (registerBits a) (SparseLookup.flatten (entries l)) [] []) u
      (state (registerBits a) (SparseLookup.flatten (entries ((a addr,a src)::l))) [] []) := by
  obtain ⟨x,hx,he⟩ := readKey_exec a addr (SparseLookup.flatten (entries l)) []
  obtain ⟨y,hy,hf⟩ := readValue_exec a src (SparseLookup.flatten (entries l)) (wordBits (a addr))
  have hg := store_exec (a addr) (a src) l (registerBits a)
  have hh := clear_key (registerBits a) (SparseLookup.flatten (entries ((a addr,a src)::l))) (wordBits (a addr)) (wordBits (a src))
  have hj := clear_value (registerBits a) (SparseLookup.flatten (entries ((a addr,a src)::l))) [] (wordBits (a src))
  have hc := (cost_arith R w 0).2
  refine ⟨_,?_,Code.Exec.seq he (Code.Exec.seq hf (Code.Exec.seq hg (Code.Exec.seq hh hj)))⟩
  simp only [wordBits,List.length_ofFn]
  omega
 theorem load_size (R w : ℕ) (dest addr : Fin R) : (load w dest.val addr.val).controlSize ≤ cost R w 0 := by
  have h₁ := RAMSlices.read_size (w*addr.val) w
  have h₂ := RAMSlices.write_size (w*dest.val) w
  have h₃ := SparseLookup.program_size w
  have ha : w*addr.val ≤ w*R := Nat.mul_le_mul_left _ (Nat.le_of_lt addr.isLt)
  have hd : w*dest.val ≤ w*R := Nat.mul_le_mul_left _ (Nat.le_of_lt dest.isLt)
  simp only [load,readKey,writeValue,lookup,Code.controlSize,Code.relabel_controlSize,Code.clear]
  unfold cost
  nlinarith
 theorem save_size (R w : ℕ) (addr src : Fin R) : (save w addr.val src.val).controlSize ≤ cost R w 0 := by
  have h₁ := RAMSlices.read_size (w*addr.val) w
  have h₂ := RAMSlices.read_size (w*src.val) w
  have ha : w*addr.val ≤ w*R := Nat.mul_le_mul_left _ (Nat.le_of_lt addr.isLt)
  have hd : w*src.val ≤ w*R := Nat.mul_le_mul_left _ (Nat.le_of_lt src.isLt)
  simp only [save,readKey,readValue,store,Code.controlSize,Code.relabel_controlSize,Code.clear,
    SparseStore.program,Code.copy,Code.transfer,Code.distribute]
  unfold cost
  nlinarith
end WLTime.RAMMemory

end OAI
