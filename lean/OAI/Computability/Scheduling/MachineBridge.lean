import OAI.Computability.Scheduling.RequestCosts

namespace OAI

section

namespace ThreeMachine.StackCompiler.Packed
variable {k : ℕ}

def halt : Packed k := ofProgram (⟨(),fun _ _ => none⟩ : Program k Unit)

theorem halt_runs (s : Store k) : halt.Runs s s 0 :=
  ⟨0,le_rfl,(),Program.Exec.halt rfl⟩

def pushWord (dst : Fin (k+1)) : List Bool → Packed k
  | [] => halt
  | b :: bs => (pushWord dst bs).seq (ofProgram (Program.push dst b))

theorem pushWord_runs (dst : Fin (k+1)) (bs : List Bool) (s : Store k) :
    (pushWord dst bs).Runs s (Function.update s dst (bs ++ s dst)) (2*bs.length) := by
  induction bs with
  | nil => simpa only [pushWord,List.nil_append,Function.update_eq_self,List.length_nil,Nat.mul_zero] using halt_runs s
  | cons b bs ih =>
    have hp : (ofProgram (Program.push dst b)).Runs (Function.update s dst (bs ++ s dst))
        (Function.update (Function.update s dst (bs ++ s dst)) dst (b :: (bs ++ s dst))) 1 := by
      change (Program.push dst b).Runs _ _ _
      simpa only [Function.update_self] using (Program.push_exec dst b (Function.update s dst (bs ++ s dst))).runs
    have h := ih.seq hp
    simpa only [pushWord,List.length_cons,Function.update_self,Function.update_idem,
      List.cons_append,Nat.mul_add,Nat.mul_one,Nat.add_assoc] using h

def pop (src : Fin (k+1)) : Packed k := ofProgram (Program.instruction (fun _ => Program.popActions src))

theorem pop_runs (src : Fin (k+1)) (s : Store k) :
    (pop src).Runs s (Function.update s src (s src).tail) 1 :=
  (Program.pop_instruction src s).runs

def popN (src : Fin (k+1)) : ℕ → Packed k
  | 0 => halt
  | n+1 => (pop src).seq (popN src n)

theorem popN_runs (src : Fin (k+1)) (n : ℕ) (s : Store k) :
    (popN src n).Runs s (Function.update s src ((s src).drop n)) (2*n) := by
  induction n generalizing s with
  | zero => simpa only [popN,List.drop_zero,Function.update_eq_self,Nat.mul_zero] using halt_runs s
  | succ n ih =>
    have h := (pop_runs src s).seq (ih (Function.update s src (s src).tail))
    have h' := h.mono (show 1+2*n+1 ≤ 2*(n+1) by omega)
    simpa only [popN,Function.update_self,Function.update_idem,List.drop_tail] using h'

end ThreeMachine.StackCompiler.Packed

namespace ThreeMachine.StackCompiler.Raw
open Packed
variable {k : ℕ}

def boolChunk (b : Bool) : List Bool := true :: (enc b).encode

theorem encoded_cons (b : Bool) (xs : List Bool) :
    (enc (b :: xs)).encode = boolChunk b ++ (enc xs).encode := rfl

def encodeBody (src dst : Fin (k+1)) : Packed k :=
  Packed.branch (fun h => (h src).getD false)
    ((Packed.pop src).seq (Packed.pushWord dst (boolChunk true)))
    ((Packed.pop src).seq (Packed.pushWord dst (boolChunk false)))

theorem encodeBody_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (bs : List Bool) (s : Store k) (hs : s src = b :: bs) :
    (encodeBody src dst).Runs s
      (Function.update (Function.update s src bs) dst (boolChunk b ++ s dst)) 12 := by
  have h := (Packed.pop_runs src s).seq
    (Packed.pushWord_runs dst (boolChunk b) (Function.update s src (s src).tail))
  simp only [hs,List.tail_cons,Function.update_of_ne hne.symm] at h
  cases b with
  | false =>
    exact (Program.Runs.branch_right _ _ h (by simp [hs])).mono (by decide)
  | true =>
    exact (Program.Runs.branch_left _ _ h (by simp [hs])).mono (by decide)

def encodeLoop (src dst : Fin (k+1)) : Packed k :=
  Packed.loop (fun h => (h src).isSome) (encodeBody src dst)

theorem encodeLoop_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (bs ys : List Bool) (s : Store k) (hs : s src = bs) (hd : s dst = (enc ys).encode) :
    (encodeLoop src dst).Runs s
      (Function.update (Function.update s src []) dst (enc (bs.reverse ++ ys)).encode)
      (14*bs.length) := by
  induction bs generalizing ys s with
  | nil =>
    have he : Function.update (Function.update s src []) dst (enc ([] ++ ys)).encode = s := by
      rw [List.nil_append,← hd]; ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all
    rw [List.reverse_nil,he]
    exact Program.Runs.loop_stop _ _ s (by simp [hs])
  | cons b bs ih =>
    let t := Function.update (Function.update s src bs) dst (boolChunk b ++ s dst)
    have hb : (encodeBody src dst).Runs s t 12 := encodeBody_runs hne b bs s hs
    have ht : t src = bs := by simp [t,hne]
    have hd' : t dst = (enc (b :: ys)).encode := by simp only [t,Function.update_self,hd,encoded_cons]
    have hr := ih (b :: ys) t ht hd'
    have he : Function.update (Function.update t src []) dst (enc (bs.reverse ++ b :: ys)).encode =
        Function.update (Function.update s src []) dst (enc ((b :: bs).reverse ++ ys)).encode := by
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
      ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all [t]
    rw [he] at hr
    exact (Program.Runs.loop_iterate _ hb hr (by simp [hs])).mono (by simp only [List.length_cons]; omega)

end ThreeMachine.StackCompiler.Raw

namespace ThreeMachine.StackCompiler.Raw
open Packed
variable {k : ℕ}

def decodeAfterTag (src dst : Fin (k+1)) : Packed k :=
  Packed.branch (fun h => (h src).getD false)
    ((Packed.popN src 3).seq (Packed.ofProgram (Program.push dst true)))
    ((Packed.popN src 1).seq (Packed.ofProgram (Program.push dst false)))

def decodeBody (src dst : Fin (k+1)) : Packed k :=
  (Packed.pop src).seq (decodeAfterTag src dst)

theorem decodeAfterTag_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (rest : List Bool) (s : Store k) (hs : s src = (enc b).encode ++ rest) :
    (decodeAfterTag src dst).Runs s
      (Function.update (Function.update s src rest) dst (b :: s dst)) 10 := by
  cases b with
  | false =>
    have h := Program.Runs.seq (Packed.popN_runs src 1 s)
      (Program.push_exec dst false (Function.update s src ((s src).drop 1))).runs
    have he : (enc false).encode = [false] := rfl
    simp only [hs,he,List.singleton_append,List.drop_succ_cons,List.drop_zero,
      Function.update_of_ne hne.symm] at h
    exact (Program.Runs.branch_right _ _ h (by simp [hs])).mono (by omega)
  | true =>
    have h := Program.Runs.seq (Packed.popN_runs src 3 s)
      (Program.push_exec dst true (Function.update s src ((s src).drop 3))).runs
    have he : (enc true).encode = [true,false,false] := rfl
    simp only [hs,he,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
      Function.update_of_ne hne.symm] at h
    exact (Program.Runs.branch_left _ _ h (by simp [hs])).mono (by omega)

theorem decodeBody_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (bs : List Bool) (s : Store k) (hs : s src = (enc (b :: bs)).encode) :
    (decodeBody src dst).Runs s
      (Function.update (Function.update s src (enc bs).encode) dst (b :: s dst)) 12 := by
  have ht : (Function.update s src (s src).tail) src = (enc b).encode ++ (enc bs).encode := by
    simp only [Function.update_self,hs,encoded_cons,boolChunk,List.cons_append,List.tail_cons]
  have h := (Packed.pop_runs src s).seq (decodeAfterTag_runs hne b (enc bs).encode _ ht)
  simpa only [decodeBody,Function.update_idem,Function.update_of_ne hne.symm,Nat.reduceAdd] using h

def decodeLoop (src dst : Fin (k+1)) : Packed k :=
  Packed.loop (fun h => (h src).getD false) (decodeBody src dst)

theorem decodeLoop_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (bs : List Bool) (s : Store k) (hs : s src = (enc bs).encode) :
    (decodeLoop src dst).Runs s
      (Function.update (Function.update s src [false]) dst (bs.reverse ++ s dst))
      (14*bs.length) := by
  induction bs generalizing s with
  | nil =>
    have he : Function.update (Function.update s src [false]) dst ([] ++ s dst) = s := by
      rw [List.nil_append]; ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all
    rw [List.reverse_nil,he]
    exact Program.Runs.loop_stop _ _ s (by change (s src).head?.getD false = _; rw [hs]; rfl)
  | cons b bs ih =>
    let t := Function.update (Function.update s src (enc bs).encode) dst (b :: s dst)
    have hb : (decodeBody src dst).Runs s t 12 := decodeBody_runs hne b bs s hs
    have hr := ih t (by simp [t,hne])
    have he : Function.update (Function.update t src [false]) dst (bs.reverse ++ t dst) =
        Function.update (Function.update s src [false]) dst ((b :: bs).reverse ++ s dst) := by
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
      ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all [t]
    rw [he] at hr
    exact (Program.Runs.loop_iterate _ hb hr (by change (s src).head?.getD false = _; rw [hs]; rfl)).mono
      (by simp only [List.length_cons]; omega)

end ThreeMachine.StackCompiler.Raw

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_zero (f : V → W) : overlay f (zeroStore V) (zeroStore W) = zeroStore W :=
  overlay_of_agree f _ _ (fun _ => rfl)

theorem overlay_start {f : V → W} (hf : Function.Injective f) (input : V) (x : Data) :
    overlay f (start input x) (zeroStore W) = start (f input) x := by
  rw [start,overlay_update hf,overlay_zero]
  rfl

theorem overlay_finish {f : V → W} (hf : Function.Injective f) (a b : V) (x y : Data) :
    overlay f (finish a b x y) (zeroStore W) = finish (f a) (f b) x y := by
  rw [finish,overlay_update hf,overlay_start hf]
  rfl

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Routine
open ThreeMachine.StackCompiler.Tree
variable {f : Data → Data} {charge : Data → ℕ}
variable (R : Routine f charge)

noncomputable def number (i : R.Vars) : Fin (Fintype.card R.Vars+1) :=
  (Fintype.equivFin R.Vars i).succ

theorem number_injective : Function.Injective R.number :=
  (Fin.succ_injective _).comp (Fintype.equivFin R.Vars).injective

@[simp] theorem number_ne_zero (i : R.Vars) : R.number i ≠ 0 := Fin.succ_ne_zero _

noncomputable def numberedCode : Code (Fin (Fintype.card R.Vars+1)) := R.code.rename R.number

theorem numberedCode_runs (x : Data) :
    R.numberedCode.compile.Runs (memory (start (R.number R.input) x))
      (memory (finish (R.number R.input) (R.number R.output) x (f x))) (150*charge x) := by
  obtain ⟨n,hn,he⟩ := R.correct x
  have hh := (he.rename R.number_injective (zeroStore (Fin (Fintype.card R.Vars+1)))).compile
  rw [overlay_start R.number_injective,overlay_finish R.number_injective] at hh
  exact hh.mono (Nat.mul_le_mul_left 150 hn)

noncomputable def initRegs : Packed (Fintype.card R.Vars+4) :=
  Packed.ofProgram (Program.instruction (fun _ j =>
    if j.val < Fintype.card R.Vars+1 then .push false else .stay))

theorem initRegs_runs (s : Store (Fintype.card R.Vars+4)) :
    R.initRegs.Runs s (fun j => if j.val < Fintype.card R.Vars+1 then false :: s j else s j) 1 := by
  have he : (fun j => (if j.val < Fintype.card R.Vars+1 then Action.push false else Action.stay).apply (s j)) =
      (fun j => if j.val < Fintype.card R.Vars+1 then false :: s j else s j) := by
    funext j
    split_ifs <;> rfl
  simpa only [initRegs,Packed.Runs,Packed.ofProgram,he] using
    (Program.instruction_exec (fun _ j =>
      if j.val < Fintype.card R.Vars+1 then Action.push false else .stay) s).runs

noncomputable def inputProgram : Packed (Fintype.card R.Vars+4) :=
  (Packed.ofProgram (Program.transfer 0 (temp 0))).seq
    (R.initRegs.seq (Raw.encodeLoop (temp 0) (reg (R.number R.input))))

@[simp] theorem temp_ne_zero : (temp (r := Fintype.card R.Vars+1) 0) ≠ 0 := by
  change temp 0 ≠ reg (0 : Fin (Fintype.card R.Vars+1))
  simp

@[simp] theorem reg_number_ne_zero (i : R.Vars) : reg (R.number i) ≠ 0 := by
  change reg (R.number i) ≠ reg (0 : Fin (Fintype.card R.Vars+1))
  simp

theorem inputProgram_runs (bs : List Bool) :
    R.inputProgram.Runs (initialStore bs)
      (memory (start (R.number R.input) (enc bs))) (17*bs.length+3) := by
  let s : Store (Fintype.card R.Vars+4) := Function.update (fun _ => []) (temp 0) bs.reverse
  have ht : (Packed.ofProgram (Program.transfer 0 (temp 0))).Runs
      (initialStore bs) s (3*bs.length) := by
    have h := (Program.transfer_exec (Ne.symm R.temp_ne_zero) (initialStore bs)).runs
    have he : Program.transferResult 0 (temp 0) (initialStore bs) = s := by
      funext i
      by_cases hi : i = temp 0 <;> by_cases hz : i = 0 <;>
        simp_all [Program.transferResult,initialStore,s,R.temp_ne_zero,Ne.symm R.temp_ne_zero]
    simpa only [Packed.Runs,Packed.ofProgram,initialStore,ite_true,he] using h
  let t : Store (Fintype.card R.Vars+4) :=
    fun j => if j.val < Fintype.card R.Vars+1 then false :: s j else s j
  have hi : R.initRegs.Runs s t 1 := R.initRegs_runs s
  have hts : t (temp 0) = bs.reverse := by simp [t,s,temp]
  have htd : t (reg (R.number R.input)) = (enc ([] : List Bool)).encode := by
    have hv : (reg (R.number R.input)).val < Fintype.card R.Vars+1 := (R.number R.input).isLt
    simp only [t,ite_eq_left hv,s,Function.update_of_ne (reg_ne_temp _ _)]
    rfl
  have he := Raw.encodeLoop_runs (temp_ne_reg _ _) bs.reverse [] t hts htd
  have hfinal : Function.update (Function.update t (temp 0) [])
      (reg (R.number R.input)) (enc (bs.reverse.reverse ++ [])).encode =
      memory (start (R.number R.input) (enc bs)) := by
    simp only [List.reverse_reverse,List.append_nil]
    funext j
    refine Fin.addCases (m := Fintype.card R.Vars+1) (n := 4) (fun i => ?_) (fun i => ?_) j
    · change Function.update (Function.update t (temp 0) []) (reg (R.number R.input))
        (enc bs).encode (reg i) = memory (start (R.number R.input) (enc bs)) (reg i)
      by_cases hh : i = R.number R.input
      · subst i; simp
      · have hv : (reg i).val < Fintype.card R.Vars+1 := i.isLt
        simp only [Function.update_of_ne (show reg i ≠ reg (R.number R.input) by simpa using hh),
          memory_reg,start_other _ hh,t,ite_eq_left hv,s,
          Function.update_of_ne (reg_ne_temp _ _)]
        rfl
    · change Function.update (Function.update t (temp 0) []) (reg (R.number R.input))
        (enc bs).encode (temp i) = memory (start (R.number R.input) (enc bs)) (temp i)
      by_cases hh : i = 0
      · subst i; simp
      · have hv : ¬(temp (r := Fintype.card R.Vars+1) i).val < Fintype.card R.Vars+1 := by
          simp only [temp,Fin.val_natAdd]; omega
        simp only [Function.update_of_ne (temp_ne_reg _ _),memory_temp,
          Function.update_of_ne (show (temp i : Fin (Fintype.card R.Vars+1+4)) ≠ temp 0 by simpa using hh),
          t,ite_eq_right hv,s]
  rw [hfinal] at he
  exact (ht.seq (hi.seq he)).mono (by simp only [List.length_reverse]; omega)

noncomputable def outputProgram : Packed (Fintype.card R.Vars+4) :=
  (Raw.decodeLoop (reg (R.number R.output)) (temp 0)).seq
    ((Packed.pop 0).seq (Packed.ofProgram (Program.transfer (temp 0) 0)))

noncomputable def rawProgram : Packed (Fintype.card R.Vars+4) :=
  R.inputProgram.seq (R.numberedCode.compile.seq R.outputProgram)

theorem outputProgram_runs (bs out : List Bool) :
    ∃ t, R.outputProgram.Runs
      (memory (finish (R.number R.input) (R.number R.output) (enc bs) (enc out))) t
      (17*out.length+3) ∧ t 0 = out := by
  let s := memory (finish (R.number R.input) (R.number R.output) (enc bs) (enc out))
  have hzero : s 0 = [false] := by
    change memory _ (reg (0 : Fin (Fintype.card R.Vars+1))) = _
    simp only [memory_reg,finish,Function.update_of_ne (Ne.symm (R.number_ne_zero R.output)),
      start_other _ (Ne.symm (R.number_ne_zero R.input))]
    rfl
  have hd := Raw.decodeLoop_runs (reg_ne_temp _ 0) out s
    (show s (reg (R.number R.output)) = (enc out).encode by simp [s])
  let u := Function.update (Function.update s (reg (R.number R.output)) [false])
    (temp 0) (out.reverse ++ s (temp 0))
  have hu : u 0 = [false] := by
    simp only [u,Function.update_of_ne (Ne.symm R.temp_ne_zero),
      Function.update_of_ne (Ne.symm (R.reg_number_ne_zero R.output)),hzero]
  have hv : u (temp 0) = out.reverse := by simp [u,s]
  let v := Function.update u 0 []
  have hp : (Packed.pop 0).Runs u v 1 := by
    simpa only [hu,List.tail_cons,List.tail_nil] using Packed.pop_runs 0 u
  have ht := (Program.transfer_exec R.temp_ne_zero v).runs
  have hvt : v (temp 0) = out.reverse := by simp [v,R.temp_ne_zero,hv]
  have hvz : v 0 = [] := by simp [v]
  rw [hvt,List.length_reverse] at ht
  have ht' : (Packed.ofProgram (Program.transfer (temp 0) 0)).Runs v
      (Program.transferResult (temp 0) 0 v) (3*out.length) := ht
  refine ⟨Program.transferResult (temp 0) 0 v,?_,?_⟩
  · exact (hd.seq (hp.seq ht')).mono (by omega)
  · simp [Program.transferResult,hvt,hvz]

theorem rawProgram_runs (bs out : List Bool) (h : f (enc bs) = enc out) :
    ∃ t, R.rawProgram.Runs (initialStore bs) t
      (1000*(charge (enc bs)+bs.length+out.length+1)) ∧ t 0 = out := by
  have hi := R.inputProgram_runs bs
  have hc := R.numberedCode_runs (enc bs)
  rw [h] at hc
  obtain ⟨t,ho,ht⟩ := R.outputProgram_runs bs out
  exact ⟨t,(hi.seq (hc.seq ho)).mono (by omega),ht⟩

include R in
theorem exists_rawMachine : ∃ k q g, ∃ M : Machine k q g,
    ∀ bs out, f (enc bs) = enc out →
      M.Produces bs out (2000*(charge (enc bs)+bs.length+out.length+1)) := by
  refine ⟨_,_,_,compile R.rawProgram.program,?_⟩
  intro bs out h
  obtain ⟨t,ht,ho⟩ := R.rawProgram_runs bs out h
  have hh := ht.computes
  obtain ⟨n,hn,hs,hh⟩ := hh
  have he := compile_produces R.rawProgram.program bs out
    (1000*(charge (enc bs)+bs.length+out.length+1)) ⟨n,hn,hh,by rw [hs,ho]⟩
  simpa only [← Nat.mul_assoc] using he

end ThreeMachine.StackCompiler.Routine
end

end OAI
