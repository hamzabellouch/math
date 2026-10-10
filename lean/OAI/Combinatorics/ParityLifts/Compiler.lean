import OAI.Combinatorics.ParityLifts.TreeMachine

namespace OAI

namespace ParityWL.Complexity

/-- Finite structured imperative code. Loops are data-dependent, not bounded by
an external oracle. The cost counts the serialized registers traversed by the
stack compiler. -/
inductive TreeCode (r : ℕ) where
  | skip
  | op (op : TreeOp r)
  | seq (first second : TreeCode r)
  | cond (src : Fin r) (nilCase nodeCase : TreeCode r)
  | loop (src : Fin r) (body : TreeCode r)

def TreeCode.compile {r : ℕ} : TreeCode r → FinTree r
  | .skip => .of (.halt true)
  | .op instr => .of ((TreeMachine.atomic instr).andThen (.halt true))
  | .seq p q => .of (p.compile.program.andThen q.compile.program)
  | .cond i p q => .of (TreeMachine.branch i p.compile.program q.compile.program)
  | .loop i p => .of ((TreeMachine.branch i (.halt true)
      (p.compile.program.andThen (.halt false))).repeat)

inductive CodeExec {r : ℕ} : TreeCode r → (Fin r → DataTree) → ℕ → (Fin r → DataTree) → Prop
  | skip (d) : CodeExec .skip d 0 d
  | op (op : TreeOp r) (d) : CodeExec (.op op) d
      (dataMass d + dataMass (op.eval d).1 + 2) (op.eval d).1
  | seq {p q d e z n m} : CodeExec p d n e → CodeExec q e m z →
      CodeExec (.seq p q) d (n + dataMass e + 1 + m) z
  | nil_cond {i p q d e n} : d i = .nil → CodeExec p d n e →
      CodeExec (.cond i p q) d (dataMass d + 1 + n) e
  | node_cond {i p q d e n} : d i ≠ .nil → CodeExec q d n e →
      CodeExec (.cond i p q) d (dataMass d + 1 + n) e
  | nil_loop {i p d} : d i = .nil → CodeExec (.loop i p) d (dataMass d + 1) d
  | node_loop {i p d e z n m} : d i ≠ .nil → CodeExec p d n e →
      CodeExec (.loop i p) e m z →
      CodeExec (.loop i p) d (dataMass d + 1 + n + 2 * (dataMass e + 1) + m) z

lemma CodeExec.compile {r : ℕ} {p : TreeCode r} {d e : Fin r → DataTree} {n : ℕ}
    (h : CodeExec p d n e) : TreeRuns p.compile.program d n e true := by
  induction h with
  | skip d => exact treeHalt_run true d
  | op op d =>
    have h := (treeAtomic_run op d).andThen (treeHalt_run true (op.eval d).1)
    convert h using 1 <;> first | rfl | omega
  | seq _ _ ih₁ ih₂ => exact ih₁.andThen ih₂
  | nil_cond h _ ih => exact ih.branch_true _ _ _ h
  | node_cond h _ ih => exact ih.branch_false _ _ _ h
  | nil_loop h =>
    simpa [TreeCode.compile, FinTree.of, TreeRuns, TreeMachine.repeat] using
      TreeExec.repeat_true ((treeHalt_run true _).branch_true _ _ _ h)
  | node_loop h _ _ ih₁ ih₂ =>
    have hr := (ih₁.andThen (treeHalt_run false _)).branch_false _ (.halt true) _ h
    have ht := TreeExec.repeat_false hr (by simpa [TreeCode.compile, FinTree.of] using ih₂)
    dsimp only [TreeRuns, TreeCode.compile, FinTree.of]
    convert ht using 1 <;> first | rfl | omega

/-- One code derivation yields a multitape computation, after input
register initialization. No complexity-class closure theorem is assumed. -/
lemma CodeExec.stack_run {r : ℕ} {p : TreeCode r} {d e : Fin r → DataTree} {n : ℕ}
    (h : CodeExec p d n e) : ∃ m, m ≤ 51 * n ∧
      Runs p.compile.program.lower.lower (dataWords d) m (dataWords e) true := by
  obtain ⟨m, hm, hr⟩ := h.compile.lower
  exact ⟨m, hm, hr.lower⟩

end ParityWL.Complexity

namespace ParityWL.Complexity

lemma Runs.repeat_true {Q : Type} {t a : ℕ} {P : StackMachine Q t a}
    {w v : Words t a} {n : ℕ} (h : Runs P w n v true) : Runs P.repeat w n v true := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, hq.repeat_true⟩

lemma Runs.repeat_false {Q : Type} {t a : ℕ} {P : StackMachine Q t a}
    {w v z : Words t a} {n m : ℕ} (h : Runs P w n v false)
    (ht : Runs P.repeat v m z true) : Runs P.repeat w (n + 1 + m) z true := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨s, hs⟩ := ht
  exact ⟨s, hq.repeat_false hs⟩

def pushWord {t a : ℕ} (dst : Fin (t + 1)) : List (StackSymbol a) → FinStack t a
  | [] => .of (.halt true)
  | c :: w => .of ((pushSymbol dst c).andThen (pushWord dst w).program)

lemma pushWord_run {t a : ℕ} (dst : Fin (t + 1)) (xs : List (StackSymbol a))
    (w : Words t a) : Runs (pushWord dst xs).program w (2 * xs.length)
      (Function.update w dst (xs.reverse ++ w dst)) true := by
  induction xs generalizing w with
  | nil => simpa [pushWord, FinStack.of] using halt_run true w
  | cons c xs ih =>
    have h := (pushSymbol_run dst c w).andThen (ih (Function.update w dst (c :: w dst)))
    have he : Function.update (Function.update w dst (c :: w dst)) dst
        (xs.reverse ++ Function.update w dst (c :: w dst) dst) =
        Function.update w dst ((c :: xs).reverse ++ w dst) := by
      simp [List.reverse_cons, List.append_assoc]
    rw [he] at h
    convert h using 1 <;> first | rfl | (simp only [List.length_cons]; omega)

def bitChunk (b : Bool) : List (StackSymbol 0) := if b then [1, 1, 0, 0] else [1, 0]

def DataTree.ofBits : List Bool → DataTree
  | [] => .nil
  | b :: bs => .node (if b then .node .nil .nil else .nil) (ofBits bs)

lemma ofBits_code (bs : List Bool) :
    (DataTree.ofBits bs).code = bs.flatMap bitChunk ++ [0] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [DataTree.ofBits, bitChunk, DataTree.code, ih]

def expandBit {t : ℕ} (src dst : Fin (t + 1)) (b : Bool) : FinStack t 0 :=
  .of (((popSymbol src).andThen (pushWord dst (bitChunk b)).program).andThen (.halt false))

def expandBitsBody {t : ℕ} (src dst : Fin (t + 1)) : FinStack t 0 :=
  .of (StackMachine.branch (fun x => (x src).isNone) (.halt true)
    (StackMachine.branch (fun x => decide (x src = some 1))
      (expandBit src dst true).program (expandBit src dst false).program))

def expandBits {t : ℕ} (src dst : Fin (t + 1)) := (expandBitsBody src dst).program.repeat

lemma expandBit_run {t : ℕ} (src dst : Fin (t + 1)) (h : src ≠ dst)
    (b : Bool) (w : Words t 0) : Runs (expandBit src dst b).program w
      (2 * (bitChunk b).length + 3)
      (Function.update (Function.update w src (w src).tail) dst ((bitChunk b).reverse ++ w dst)) false := by
  have hr := ((popSymbol_run src w).andThen
    (pushWord_run dst (bitChunk b) (Function.update w src (w src).tail))).andThen
    (halt_run false _)
  simp only [Function.update_of_ne h.symm] at hr
  convert hr using 1 <;> first | rfl | omega

lemma expandBits_run {t : ℕ} (src dst : Fin (t + 1)) (h : src ≠ dst)
    (bs : List Bool) (w : Words t 0) (hw : w src = bs.map (stackInputSymbol 0)) :
    Runs (expandBits src dst) w (2 * (bs.flatMap bitChunk).length + 6 * bs.length + 1)
      (Function.update (Function.update w src []) dst ((bs.flatMap bitChunk).reverse ++ w dst)) true := by
  induction bs generalizing w with
  | nil =>
    have hr := Runs.branch_true (fun x => (x src).isNone) (StackMachine.halt true)
      (StackMachine.branch (fun x => decide (x src = some 1))
        (expandBit src dst true).program (expandBit src dst false).program)
      (w := w) (by simp [hw]) (halt_run true w)
    have hh := hr.repeat_true
    have hw0 : w src = [] := by simpa using hw
    have he : Function.update (Function.update w src []) dst (w dst) = w := by
      rw [← hw0, Function.update_eq_self, Function.update_eq_self]
    simpa only [List.flatMap_nil, List.length_nil, Nat.mul_zero, Nat.zero_add,
      List.reverse_nil, List.nil_append, he, expandBits, expandBitsBody, FinStack.of] using hh
  | cons b bs ih =>
    let v := Function.update (Function.update w src (w src).tail) dst ((bitChunk b).reverse ++ w dst)
    have hv : v src = bs.map (stackInputSymbol 0) := by simp [v, h, hw]
    have hr := expandBit_run src dst h b w
    have hr' : Runs (expandBitsBody src dst).program w
        (2 * (bitChunk b).length + 5) v false := by
      cases b with
      | false =>
        have ht := hr.branch_false (fun x => decide (x src = some 1)) (expandBit src dst true).program _
          (by simp [hw, stackInputSymbol])
        have hh := ht.branch_false (fun x => (x src).isNone) (StackMachine.halt true) _ (by simp [hw])
        convert hh using 1
        rfl
      | true =>
        have ht := hr.branch_true (fun x => decide (x src = some 1)) _ (expandBit src dst false).program
          (by simp [hw, stackInputSymbol])
        have hh := ht.branch_false (fun x => (x src).isNone) (StackMachine.halt true) _ (by simp [hw])
        convert hh using 1
        rfl
    have ht := hr'.repeat_false (ih v hv)
    have he : Function.update (Function.update v src []) dst
        ((bs.flatMap bitChunk).reverse ++ v dst) =
        Function.update (Function.update w src []) dst
          (((b :: bs).flatMap bitChunk).reverse ++ w dst) := by
      ext i
      by_cases hid : i = dst
      · subst i; simp [v, List.reverse_append, List.append_assoc]
      · by_cases his : i = src
        · subst i; simp [hid, v]
        · simp [Function.update_of_ne hid, Function.update_of_ne his, v]
    rw [he] at ht
    convert ht using 1 <;> first | rfl |
      (simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega)

def readBits {t : ℕ} (src tmp : Fin (t + 1)) :=
  ((expandBits src tmp).andThen (pushSymbol tmp 0)).andThen (transfer tmp {src})

lemma bitChunk_length (b : Bool) : (bitChunk b).length ≤ 4 := by cases b <;> decide

lemma flatMap_bitChunk_length (bs : List Bool) : (bs.flatMap bitChunk).length ≤ 4 * bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]
                    have := bitChunk_length b
                    omega

lemma readBits_run {t : ℕ} (src tmp : Fin (t + 1)) (h : src ≠ tmp)
    (bs : List Bool) (w : Words t 0) (hw : w src = bs.map (stackInputSymbol 0))
    (ht : w tmp = []) : ∃ n, n ≤ 22 * bs.length + 7 ∧
      Runs (readBits src tmp) w n (Function.update w src (DataTree.ofBits bs).code) true := by
  let v := Function.update (Function.update w src []) tmp ((bs.flatMap bitChunk).reverse ++ w tmp)
  have h₁ := expandBits_run src tmp h bs w hw
  have h₂ := pushSymbol_run tmp 0 v
  let z := Function.update v tmp (0 :: v tmp)
  have h₃ := transfer_run tmp {src} z
  have hz : z tmp = 0 :: (bs.flatMap bitChunk).reverse := by simp [z, v, ht]
  have he : transferred tmp {src} z = Function.update w src (DataTree.ofBits bs).code := by
    ext i
    by_cases hi : i = tmp
    · subst i; simp [transferred, Function.update, h.symm, ht]
    · by_cases hs : i = src
      · subst i
        simp [transferred, h, z, v, ofBits_code, ht]
      · simp [transferred, hi, hs, z, v]
  have hr := (h₁.andThen h₂).andThen h₃
  rw [he, hz, List.length_cons, List.length_reverse] at hr
  refine ⟨_, ?_, hr⟩
  have := flatMap_bitChunk_length bs
  omega

def inputData (r : ℕ) (bs : List Bool) : Fin (r + 1) → DataTree :=
  fun i => if i = 0 then DataTree.ofBits bs else .nil

def inputStacks (r : ℕ) (bs : List Bool) : Words (r + 4) 0 :=
  fun i => if i.val = 0 then bs.map (stackInputSymbol 0) else []

def fillData (r : ℕ) :=
  primitive (t := r + 4) (a := 0)
    (fun _ i => if 0 < i.val ∧ i.val < r + 1 then .push 0 else .keep) (fun _ => true)

def initializeData (r : ℕ) :=
  (readBits (dataReg (0 : Fin (r + 1))) (workReg (r + 1) 0)).andThen (fillData r)

lemma initializeData_run (r : ℕ) (bs : List Bool) :
    ∃ n, n ≤ 22 * bs.length + 9 ∧
      Runs (initializeData r) (inputStacks r bs) n (dataWords (inputData r bs)) true := by
  have hs : inputStacks r bs (dataReg (0 : Fin (r + 1))) = bs.map (stackInputSymbol 0) := by
    simp [inputStacks, dataReg]
  have ht : inputStacks r bs (workReg (r + 1) 0) = [] := by simp [inputStacks, workReg]
  obtain ⟨n, hn, hr⟩ := readBits_run (dataReg (0 : Fin (r + 1))) (workReg (r + 1) 0)
    (dataReg_ne_workReg _ _) bs (inputStacks r bs) hs ht
  let w := Function.update (inputStacks r bs) (dataReg (0 : Fin (r + 1))) (DataTree.ofBits bs).code
  have hf := primitive_exec (t := r + 4) (a := 0)
    (fun _ i => if 0 < i.val ∧ i.val < r + 1 then .push 0 else .keep) (fun _ => true) w
  have he : applyOps (fun i => if 0 < i.val ∧ i.val < r + 1 then .push 0 else .keep) w =
      dataWords (inputData r bs) := by
    funext i
    refine Fin.addCases (m := r + 1) (n := 4) (fun j => ?_) (fun j => ?_) i
    · change applyOps _ w (dataReg j) = dataWords (inputData r bs) (dataReg j)
      rw [dataWords_data]
      by_cases hj : j = 0
      · subst j; simp [applyOps, dataReg, StackOp.apply, w, inputData]
      · have hv : j.val ≠ 0 := by simpa using hj
        simp [applyOps, StackOp.apply, w, inputData, hj, inputStacks, dataReg, DataTree.code,
          show 0 < j.val by omega, j.isLt]
    · change applyOps _ w (workReg (r + 1) j) = dataWords (inputData r bs) (workReg (r + 1) j)
      rw [dataWords_work]
      have hv : ¬(0 < (workReg (r + 1) j).val ∧ (workReg (r + 1) j).val < r + 1) := by
        simp only [workReg, Fin.val_natAdd]
        omega
      simp only [applyOps, ite_eq_right hv, StackOp.apply, w,
        Function.update_of_ne (Ne.symm (dataReg_ne_workReg (0 : Fin (r + 1)) j))]
      simp [inputStacks, workReg]
  have hf' : Runs (fillData r) w 1 (dataWords (inputData r bs)) true := ⟨some true, he ▸ hf⟩
  exact ⟨n + 1 + 1, by omega, hr.andThen hf'⟩

end ParityWL.Complexity

end OAI
