import OAI.Combinatorics.VariableWL.StackSimulation

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.StackSimulation
open Turing TM2to1 TM2to1.Λ' VariableWL.BoundedSimulation
variable {K : Type uVariable1} {Γ : K → Type uVariable9} {Λ : Type uVariable2} {σ : Type uVariable3} [DecidableEq K]
variable (M : Λ → TM2.Stmt Γ Λ σ) (C : ℕ) (hC : ∀ l, operations (M l) ≤ C)
include hC

 theorem next_length (c : TM2.Cfg Γ Λ σ) (B : ℕ) (hc : ∀ k, (c.stk k).length ≤ B) :
    ∀ k, (((TM2.step M c).getD c).stk k).length ≤ B+C := by
  rcases c with ⟨q,v,S⟩
  cases q with
  | none => exact fun k => (hc k).trans (Nat.le_add_right B C)
  | some q =>
    exact fun k => (stepAux_length (M q) v S B hc k).trans (Nat.add_le_add_left (hC q) B)

 theorem evolve_length (c : TM2.Cfg Γ Λ σ) (B : ℕ) (hc : ∀ k, (c.stk k).length ≤ B) (n : ℕ) :
    ∀ k, ((evolve (TM2.step M) c n).stk k).length ≤ B+n*C := by
  induction n with
  | zero => simpa only [evolve,Nat.zero_mul,Nat.add_zero] using hc
  | succ n ih =>
    intro k
    have h := next_length M C hC _ _ ih k
    simpa only [evolve,Nat.succ_mul,Nat.add_assoc] using h

 theorem one_bound (c : TM2.Cfg Γ Λ σ) (d : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (h : TrCfg c d) (B : ℕ) (hc : ∀ k, (c.stk k).length ≤ B) :
    ∃ d', TrCfg ((TM2.step M c).getD c) d' ∧
      Within (TM1.step (tr M)) d d' (1+C*(2*(B+C)+2)) := by
  cases h with
  | @mk q v S L hL =>
    cases q with
    | none =>
      refine ⟨_,TrCfg.mk L hL,(Within.zero _).mono (Nat.zero_le _)⟩
    | some q =>
      obtain ⟨d',hd',hp⟩ := normal_bound M (M q) v S L hL B hc
      refine ⟨d',hd',?_⟩
      have hs : TM1.step (tr M) ⟨some (normal q),v,Tape.mk' ∅ (addBottom L)⟩ =
          some (TM1.stepAux (trNormal (M q)) v (Tape.mk' ∅ (addBottom L))) := rfl
      apply (hp.head hs).mono
      have hh := hC q
      have hb : operations (M q)*(2*(B+operations (M q))+2) ≤ C*(2*(B+C)+2) :=
        Nat.mul_le_mul hh (by omega)
      omega

 theorem run_bound (c : TM2.Cfg Γ Λ σ) (d : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (h : TrCfg c d) (B : ℕ) (hc : ∀ k, (c.stk k).length ≤ B) (n : ℕ) :
    ∃ d', TrCfg (evolve (TM2.step M) c n) d' ∧
      Within (TM1.step (tr M)) d d' (n*(1+C*(2*(B+n*C+C)+2))) := by
  induction n with
  | zero => exact ⟨d,h,by simpa only [Nat.zero_mul] using (Within.zero (f := TM1.step (tr M)) d)⟩
  | succ n ih =>
    obtain ⟨dn,hdn,hpn⟩ := ih
    obtain ⟨dn',hdn',hpn'⟩ := one_bound M C hC _ dn hdn (B+n*C) (evolve_length M C hC c B hc n)
    refine ⟨dn',hdn',(hpn.trans hpn').mono ?_⟩
    have hb : 1+C*(2*(B+n*C+C)+2) ≤ 1+C*(2*(B+(n+1)*C+C)+2) := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    calc
      n*(1+C*(2*(B+n*C+C)+2))+(1+C*(2*(B+n*C+C)+2))
          = (n+1)*(1+C*(2*(B+n*C+C)+2)) := by ring
      _ ≤ (n+1)*(1+C*(2*(B+(n+1)*C+C)+2)) := Nat.mul_le_mul_left _ hb

end VariableWL.StackSimulation

namespace VariableWL.BoundedSimulation.Steps
variable {S : Type uVariable4} {f : S → Option S} {n : ℕ} {a b c : S}

theorem rebase (he : f a=f b) (hn : 0<n) (h : Steps f n b c) : Steps f n a c := by
  cases h with
  | zero => omega
  | succ hs ht => exact Steps.succ (he.trans hs) ht

end VariableWL.BoundedSimulation.Steps

namespace VariableWL.UnitSimulation
open Turing VariableWL.BoundedSimulation
variable {Γ : Type uVariable5} {Λ : Type uVariable6} {σ : Type uVariable7} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

def instructions : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => instructions q+1
  | .write _ q => instructions q+1
  | .load _ q => instructions q
  | .branch _ q r => max (instructions q) (instructions r)
  | .goto _ | .halt => 1

variable (M : Λ → TM1.Stmt Γ Λ σ)

theorem statement_bound (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    ∃ n, 0<n ∧ n ≤ instructions q ∧
      Steps (TM0.step (TM1to0.tr M)) n ⟨(some q,v),T⟩
        (TM1to0.trCfg M (TM1.stepAux q v T)) := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨n,hn,hnq,h⟩ := ih v (T.move d)
    refine ⟨n+1,by omega,by simpa only [instructions] using Nat.add_le_add_right hnq 1,?_⟩
    exact Steps.head rfl h
  | write a q ih =>
    obtain ⟨n,hn,hnq,h⟩ := ih v (T.write (a T.1 v))
    refine ⟨n+1,by omega,by simpa only [instructions] using Nat.add_le_add_right hnq 1,?_⟩
    exact Steps.head rfl h
  | load a q ih =>
    obtain ⟨n,hn,hnq,h⟩ := ih (a T.1 v) T
    refine ⟨n,hn,hnq,?_⟩
    have he : TM0.step (TM1to0.tr M) ⟨(some (.load a q),v),T⟩ =
        TM0.step (TM1to0.tr M) ⟨(some q,a T.1 v),T⟩ := rfl
    simpa only [TM1.stepAux] using h.rebase he hn
  | branch p q r ihq ihr =>
    cases hp : p T.1 v
    · obtain ⟨n,hn,hnr,h⟩ := ihr v T
      refine ⟨n,hn,hnr.trans (le_max_right _ _),?_⟩
      have he : TM0.step (TM1to0.tr M) ⟨(some (.branch p q r),v),T⟩ =
          TM0.step (TM1to0.tr M) ⟨(some r,v),T⟩ := by
        simp only [TM0.step,TM1to0.tr,TM1to0.trAux,hp,Bool.cond_false]
      simpa only [TM1.stepAux,hp,Bool.cond_false] using h.rebase he hn
    · obtain ⟨n,hn,hnq,h⟩ := ihq v T
      refine ⟨n,hn,hnq.trans (le_max_left _ _),?_⟩
      have he : TM0.step (TM1to0.tr M) ⟨(some (.branch p q r),v),T⟩ =
          TM0.step (TM1to0.tr M) ⟨(some q,v),T⟩ := by
        simp only [TM0.step,TM1to0.tr,TM1to0.trAux,hp,Bool.cond_true]
      simpa only [TM1.stepAux,hp,Bool.cond_true] using h.rebase he hn
  | goto f =>
    refine ⟨1,by omega,le_rfl,Steps.single ?_⟩
    simp only [TM0.step,TM1to0.tr,TM1to0.trAux,TM1.stepAux,TM1to0.trCfg,
      Option.map_some,Tape.write_self]
  | halt =>
    refine ⟨1,by omega,le_rfl,Steps.single ?_⟩
    simp only [TM0.step,TM1to0.tr,TM1to0.trAux,TM1.stepAux,TM1to0.trCfg,
      Option.map_none,Option.map_some,Tape.write_self]

 theorem one_bound (S : Finset Λ) (C : ℕ) (hC : ∀ l ∈ S, instructions (M l) ≤ C)
    (c : TM1.Cfg Γ Λ σ) (hc : c.l ∈ Finset.insertNone S) :
    Within (TM0.step (TM1to0.tr M)) (TM1to0.trCfg M c)
      (TM1to0.trCfg M ((TM1.step M c).getD c)) C := by
  rcases c with ⟨q,v,T⟩
  cases q with
  | none => exact (Within.zero _).mono (Nat.zero_le _)
  | some q =>
    obtain ⟨n,_,hn,h⟩ := statement_bound M (M q) v T
    exact ⟨n,hn.trans (hC q (Finset.some_mem_insertNone.mp hc)),h⟩

omit [Inhabited σ] in
 theorem steps_support (S : Finset Λ) (hS : TM1.Supports M S) {a b : TM1.Cfg Γ Λ σ}
    {n : ℕ} (h : Steps (TM1.step M) n a b) (ha : a.l ∈ Finset.insertNone S) :
    b.l ∈ Finset.insertNone S := by
  induction h with
  | zero => exact ha
  | succ hs ht ih => exact ih (TM1.step_supports M hS hs ha)

 theorem steps_bound (S : Finset Λ) (hS : TM1.Supports M S) (C : ℕ)
    (hC : ∀ l ∈ S, instructions (M l) ≤ C) {a b : TM1.Cfg Γ Λ σ}
    {n : ℕ} (h : Steps (TM1.step M) n a b) (ha : a.l ∈ Finset.insertNone S) :
    Within (TM0.step (TM1to0.tr M)) (TM1to0.trCfg M a) (TM1to0.trCfg M b) (n*C) := by
  induction h with
  | zero => simpa only [Nat.zero_mul] using (Within.zero (f := TM0.step (TM1to0.tr M)) _)
  | @succ n a b c hs ht ih =>
    have hb := TM1.step_supports M hS hs ha
    have hfirst := one_bound M S C hC a ha
    rw [hs,Option.getD_some] at hfirst
    have hr := hfirst.trans (ih hb)
    simpa only [Nat.succ_mul,Nat.add_comm C] using hr

end VariableWL.UnitSimulation

namespace VariableWL.MultiStack
open Turing
variable (M : Machine)
abbrev K := Fin (M.extraTapes+1)
abbrev Γ := Fin (M.workSymbols+3)
abbrev Q := Fin (M.states+1)
abbrev Slot := K M × Bool
abbrev Stacks := Slot M → List (Γ M)
abbrev Data := Q M × (K M → Γ M × Motion)

inductive Label where
  | simulate : Q M → Label
  | drain : Bool → Label
  deriving DecidableEq

instance : Fintype (Label M) := Fintype.ofEquiv (Q M ⊕ Bool)
  ⟨(fun | .inl q => .simulate q | .inr b => .drain b),
   (fun | .simulate q => .inl q | .drain b => .inr b),
   (by intro q; cases q <;> rfl),(by intro q; cases q <;> rfl)⟩
instance : Inhabited (Label M) := ⟨.simulate 0⟩

@[ext] structure Vars where
  reads : K M → Γ M
  data : Option (Data M)
  answer : Bool

abbrev Statement := TM2.Stmt (fun _ : Slot M => Γ M) (Label M) (Vars M)
abbrev Config := TM2.Cfg (fun _ : Slot M => Γ M) (Label M) (Vars M)

instance : Inhabited (Vars M) := ⟨⟨fun _ => 0,none,false⟩⟩

def getData (v : Vars M) : Data M := v.data.getD (0,fun _ => (0,.stay))
def tape (S : Stacks M) (j : K M) : Tape (Γ M) := Tape.mk₂ (S (j,false)) (S (j,true))

def readVars (ls : List (K M)) (v : Vars M) (S : Stacks M) : Vars M :=
  {v with reads := fun j => if j ∈ ls then (S (j,true)).headI else v.reads j}

def readAll : List (K M) → Statement M → Statement M
  | [], q => q
  | j::ls, q => .peek (j,true) (fun v a => {v with reads := Function.update v.reads j (a.getD 0)})
      (readAll ls q)

theorem readAll_sem (ls : List (K M)) (q : Statement M) (v : Vars M) (S : Stacks M) :
    TM2.stepAux (readAll M ls q) v S=TM2.stepAux q (readVars M ls v S) S := by
  induction ls generalizing v with
  | nil => simp only [readAll,readVars,List.not_mem_nil,ite_false]
  | cons j ls ih =>
    simp only [readAll,TM2.stepAux,ih]
    congr 1
    apply Vars.ext <;> try rfl
    funext k
    simp only [readVars,List.mem_cons]
    by_cases hk : k ∈ ls
    · simp only [hk,or_true,ite_true]
    · simp only [hk,or_false,ite_false]
      by_cases he : k=j
      · subst k; cases S (j,true) <;> simp [List.headI]
      · simp only [he,ite_false,Function.update_of_ne he]

noncomputable def allTapes : List (K M) := List.ofFn id

theorem readVars_all (v : Vars M) (S : Stacks M) :
    readVars M (allTapes M) v S={v with reads := fun j => (S (j,true)).headI} := by
  apply Vars.ext <;> try rfl
  funext j
  simp only [readVars,allTapes,List.mem_ofFn]
  simp

def writeVars (v : Vars M) (S : Stacks M) (j : K M) (m : Motion) : Vars M :=
  match m with
  | .left => {v with reads := Function.update v.reads j (S (j,false)).headI}
  | _ => v

def writeStacks (S : Stacks M) (j : K M) (a : Γ M) : Motion → Stacks M
  | .left => Function.update (Function.update S (j,false) (S (j,false)).tail)
      (j,true) ((S (j,false)).headI::a::(S (j,true)).tail)
  | .right => Function.update (Function.update S (j,false) (a::S (j,false)))
      (j,true) (S (j,true)).tail
  | .stay => Function.update S (j,true) (a::(S (j,true)).tail)

def writeTape (j : K M) (q : Statement M) : Statement M :=
  .pop (j,true) (fun v _ => v)
    (.branch (fun v => decide (((getData M v).2 j).2 = .left))
      (.pop (j,false) (fun v a => {v with reads := Function.update v.reads j (a.getD 0)})
        (.push (j,true) (fun v => ((getData M v).2 j).1)
          (.push (j,true) (fun v => v.reads j) q)))
      (.branch (fun v => decide (((getData M v).2 j).2 = .right))
        (.push (j,false) (fun v => ((getData M v).2 j).1) q)
        (.push (j,true) (fun v => ((getData M v).2 j).1) q)))

theorem writeTape_sem (j : K M) (q : Statement M) (v : Vars M) (S : Stacks M) :
    TM2.stepAux (writeTape M j q) v S =
      TM2.stepAux q (writeVars M v S j ((getData M v).2 j).2)
        (writeStacks M S j ((getData M v).2 j).1 ((getData M v).2 j).2) := by
  have hf : (j,false) ≠ (j,true) := by simp
  have ht : (j,true) ≠ (j,false) := Ne.symm hf
  have hh (l : List (Γ M)) : l.head?.getD 0=l.headI := by cases l <;> rfl
  cases hm : ((getData M v).2 j).2 <;>
    simp only [writeTape,TM2.stepAux,hm,decide_true,decide_false,Bool.cond_true,Bool.cond_false,
      reduceCtorEq,
      writeVars,writeStacks,Function.update_self,Function.update_of_ne hf,Function.update_of_ne ht,hh]
  all_goals simp only [getData,Function.update_idem,Function.update_comm hf]

theorem writeVars_data (v : Vars M) (S : Stacks M) (j : K M) (m : Motion) :
    (writeVars M v S j m).data=v.data := by cases m <;> rfl

theorem writeStacks_other (S : Stacks M) (j k : K M) (h : k ≠ j) (a : Γ M) (m : Motion) (b : Bool) :
    writeStacks M S j a m (k,b)=S (k,b) := by
  have hf : (k,b) ≠ (j,false) := by simp [h]
  have ht : (k,b) ≠ (j,true) := by simp [h]
  cases m <;> simp only [writeStacks,Function.update_of_ne hf,Function.update_of_ne ht]

def applyMotion (T : Tape (Γ M)) : Motion → Tape (Γ M)
  | .left => T.move .left
  | .stay => T
  | .right => T.move .right

theorem tape_writeStacks (S : Stacks M) (j : K M) (a : Γ M) (m : Motion) :
    tape M (writeStacks M S j a m) j=applyMotion M ((tape M S j).write a) m := by
  have hf : (j,false) ≠ (j,true) := by simp
  have ht : (j,true) ≠ (j,false) := Ne.symm hf
  cases m <;> simp [tape,writeStacks,applyMotion,Tape.mk₂,Tape.write_mk',
    ListBlank.head_mk,ListBlank.tail_mk,ListBlank.cons_mk,List.headI,hf]

def writeAll : List (K M) → Statement M → Statement M
  | [],q => q
  | j::ls,q => writeTape M j (writeAll ls q)

def applyStacks : List (K M) → Data M → Stacks M → Stacks M
  | [],_,S => S
  | j::ls,d,S => applyStacks ls d (writeStacks M S j (d.2 j).1 (d.2 j).2)

theorem writeAll_sem (ls : List (K M)) (q : Statement M) (v : Vars M) (S : Stacks M) :
    ∃ v', v'.data=v.data ∧ TM2.stepAux (writeAll M ls q) v S=
      TM2.stepAux q v' (applyStacks M ls (getData M v) S) := by
  induction ls generalizing v S with
  | nil => exact ⟨v,rfl,rfl⟩
  | cons j ls ih =>
    rw [writeAll,writeTape_sem]
    obtain ⟨v',hv',hh⟩ := ih (writeVars M v S j ((getData M v).2 j).2)
      (writeStacks M S j ((getData M v).2 j).1 ((getData M v).2 j).2)
    refine ⟨v',hv'.trans (writeVars_data M v S j _),?_⟩
    simpa only [applyStacks,getData,writeVars_data] using hh

theorem tape_applyStacks (ls : List (K M)) (hn : ls.Nodup) (d : Data M) (S : Stacks M) (j : K M) :
    tape M (applyStacks M ls d S) j =
      if j ∈ ls then applyMotion M ((tape M S j).write (d.2 j).1) (d.2 j).2 else tape M S j := by
  induction ls generalizing S with
  | nil => rfl
  | cons k ls ih =>
    rw [applyStacks,ih hn.tail]
    by_cases he : j=k
    · subst j
      simp only [(List.nodup_cons.mp hn).1,ite_false,List.mem_cons_self,ite_true,tape_writeStacks]
    · have ho : tape M (writeStacks M S k (d.2 k).1 (d.2 k).2) j=tape M S j := by
        simp only [tape,writeStacks_other M S k j he]
      rw [ho]
      simp only [List.mem_cons,he,false_or]

noncomputable def program : Label M → Statement M
  | .simulate q => readAll M (allTapes M)
      (.load (fun v => {v with data := M.transition q v.reads})
        (.branch (fun v => v.data.isSome)
          (writeAll M (allTapes M) (.goto (fun v => .simulate (getData M v).1)))
          (.load (fun v => {v with answer := false}) (.goto (fun _ => .drain false)))))
  | .drain b => .pop (0,b) (fun v a =>
      { data := none
        answer := v.answer || decide (a=some 2)
        reads := Function.update v.reads 0 (if a.isSome then 1 else 0) })
      (.branch (fun v => decide (v.reads 0=0))
        (if b then .halt else .goto (fun _ => .drain true))
        (.goto (fun _ => .drain b)))

end VariableWL.MultiStack

namespace VariableWL.MultiStack
open Turing BoundedSimulation
variable (M : Machine)

def Related (c : Configuration M) (s : Config M) : Prop :=
  s.l=some (.simulate c.control) ∧
    ∀ j i, (tape M s.stk j).nth i=c.cells j (c.heads j+i)

theorem applyMotion_nth (T : Tape (Γ M)) (m : Motion) (i : ℤ) :
    (applyMotion M T m).nth i=T.nth (i+m.displacement) := by
  cases m <;> simp [applyMotion,Motion.displacement,sub_eq_add_neg]

theorem allTapes_mem (j : K M) : j ∈ allTapes M := by
  exact List.mem_ofFn.mpr ⟨j,rfl⟩
theorem allTapes_nodup : (allTapes M).Nodup := by
  unfold allTapes
  exact List.nodup_ofFn.mpr Function.injective_id

theorem simulate_step {c c' : Configuration M} (s : Config M) (h : Related M c s)
    (hs : step M c=some c') :
    ∃ s', TM2.step (program M) s=some s' ∧ Related M c' s' := by
  obtain ⟨hl,ht⟩ := h
  obtain ⟨d,hd,rfl⟩ := Option.map_eq_some_iff.mp hs
  have hr : (fun j => (s.stk (j,true)).headI)=scanned c := by
    funext j
    simpa only [tape,Tape.mk₂,Tape.mk',ListBlank.head_mk,scanned,Tape.nth_zero,Int.add_zero] using ht j 0
  let v : Vars M := {s.var with reads := scanned c, data := some d}
  obtain ⟨v',hv',he⟩ := writeAll_sem M (allTapes M)
    (.goto (fun v => .simulate (getData M v).1)) v s.stk
  have hv : getData M v'=d := by simp only [getData,hv',v,Option.getD_some]
  let s' : Config M := ⟨some (.simulate d.1),v',applyStacks M (allTapes M) d s.stk⟩
  refine ⟨s',?_,rfl,?_⟩
  · cases s with
    | mk l var stk =>
      dsimp only at hl
      subst l
      simp only [TM2.step,program,readAll_sem,readVars_all,TM2.stepAux,hr,hd,
        Option.isSome_some,Bool.cond_true]
      change some (TM2.stepAux (writeAll M (allTapes M) _) v stk)=some s'
      rw [he]
      simp only [TM2.stepAux,s']
      rw [hv]
      rfl
  · intro j i
    change (tape M (applyStacks M (allTapes M) d s.stk) j).nth i = _
    rw [tape_applyStacks M _ (allTapes_nodup M),ite_eq_left (allTapes_mem M j),
      applyMotion_nth,Tape.write_nth]
    change (if i+(d.2 j).2.displacement=0 then (d.2 j).1 else
      (tape M s.stk j).nth (i+(d.2 j).2.displacement)) =
      if c.heads j+(d.2 j).2.displacement+i=c.heads j then (d.2 j).1
      else c.cells j (c.heads j+(d.2 j).2.displacement+i)
    rw [ht]
    have he : i+(d.2 j).2.displacement=0 ↔ c.heads j+(d.2 j).2.displacement+i=c.heads j := by omega
    simp only [he]
    congr 2
    omega

theorem simulate_steps {c c' : Configuration M} {n : ℕ} (s : Config M) (h : Related M c s)
    (hs : Steps (step M) n c c') :
    ∃ s', Steps (TM2.step (program M)) n s s' ∧ Related M c' s' := by
  induction hs generalizing s with
  | zero => exact ⟨s,Steps.zero s,h⟩
  | succ hs ht ih =>
    obtain ⟨s',hstep,hrel⟩ := simulate_step M s h hs
    obtain ⟨s'',hrun,hrel'⟩ := ih s' hrel
    exact ⟨s'',Steps.head hstep hrun,hrel'⟩

theorem simulate_halt (c : Configuration M) (s : Config M) (h : Related M c s)
    (hs : step M c=none) :
    TM2.step (program M) s = some
      ⟨some (.drain false),{reads := scanned c, data := none, answer := false},s.stk⟩ := by
  obtain ⟨hl,ht⟩ := h
  have hd : M.transition c.control (scanned c)=none := Option.map_eq_none_iff.mp hs
  have hr : (fun j => (s.stk (j,true)).headI)=scanned c := by
    funext j
    simpa only [tape,Tape.mk₂,Tape.mk',ListBlank.head_mk,scanned,Tape.nth_zero,Int.add_zero] using ht j 0
  cases s with
  | mk l var stk =>
    dsimp only at hl
    subst l
    simp only [TM2.step,program,readAll_sem,readVars_all,TM2.stepAux,hr,hd,
      Option.isSome_none,Bool.cond_false]

end VariableWL.MultiStack

namespace VariableWL.MultiStack
open Turing BoundedSimulation
variable (M : Machine)

def inputSymbol (b : Bool) : Γ M := if b then 2 else 1

def initialStacks (w : Word) : Stacks M :=
  Function.update (fun _ => []) (0,true) (w.map (inputSymbol M))

def initialConfig (w : Word) : Config M := ⟨some (.simulate 0),default,initialStacks M w⟩

theorem initialConfig_eq (w : Word) : initialConfig M w=TM2.init (0,true) (w.map (inputSymbol M)) := rfl

theorem tape_nth_nat (S : Stacks M) (j : K M) (i : ℕ) :
    (tape M S j).nth i=(S (j,true)).getI i := by simp [tape,Tape.mk₂]
theorem tape_nth_neg (S : Stacks M) (j : K M) (i : ℕ) :
    (tape M S j).nth (-(i+1 : ℕ) : ℤ)=(S (j,false)).getI i := rfl

theorem initial_related (w : Word) : Related M (initial M w) (initialConfig M w) := by
  refine ⟨rfl,?_⟩
  intro j i
  change (tape M (initialStacks M w) j).nth i=(if j=0 then wordCells M.workSymbols w else fun _ => 0) (0+i)
  rw [Int.zero_add]
  cases i with
  | ofNat i =>
    change (tape M (initialStacks M w) j).nth (i : ℤ)=_
    rw [tape_nth_nat M (initialStacks M w) j i]
    by_cases hj : j=0
    · subst j
      simp only [initialStacks,Function.update_self,ite_true]
      change (List.map (inputSymbol M) w).getI i=wordCells M.workSymbols w (i : ℤ)
      simp only [wordCells,Int.natCast_nonneg,ite_true,Int.toNat_natCast,
        List.getI_eq_getElem?_getD,List.getElem?_map]
      cases hw : w[i]? with
      | none => rfl
      | some b => cases b <;> rfl
    · have h : (j,true) ≠ (0,true) := by simp [hj]
      simp only [initialStacks,Function.update_of_ne h,ite_eq_right hj,List.getI_nil]
      rfl
  | negSucc i =>
    have hn : Int.negSucc i=(-(i+1:ℕ):ℤ) := by omega
    rw [hn,tape_nth_neg]
    have h : (j,false) ≠ (0,true) := by simp
    simp only [initialStacks,Function.update_of_ne h,List.getI_nil]
    have hneg : ¬ (0 : ℤ) ≤ -(i+1:ℕ) := by omega
    by_cases hj : j=0
    · simp only [hj,ite_true,wordCells,hneg,ite_false]
      rfl
    · simp only [hj,ite_false]
      rfl

theorem initial_lengths (w : Word) (j : Slot M) : ((initialConfig M w).stk j).length ≤ w.length := by
  change (initialStacks M w j).length ≤ _
  by_cases hj : j=(0,true)
  · subst j; simp [initialStacks]
  · simp [initialStacks,Function.update_of_ne hj]

end VariableWL.MultiStack

namespace VariableWL.BoundedSimulation
variable {S : Type uVariable8}
theorem evolve_steps (f : S → Option S) (a : S) (n : ℕ) :
    ∃ t ≤ n, Steps f t a (evolve f a n) := by
  induction n with
  | zero => exact ⟨0,le_rfl,Steps.zero a⟩
  | succ n ih =>
    obtain ⟨t,ht,h⟩ := ih
    cases he : f (evolve f a n) with
    | none => exact ⟨t,by omega,by simpa only [evolve,he,Option.getD_none] using h⟩
    | some c => exact ⟨t+1,by omega,by simpa only [evolve,he,Option.getD_some] using h.tail he⟩
end VariableWL.BoundedSimulation

namespace VariableWL
 theorem run_eq_evolve (M : Machine) (w : Word) (n : ℕ) :
    run M w n=BoundedSimulation.evolve (step M) (initial M w) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run,BoundedSimulation.evolve,ih]
end VariableWL

end OAI
