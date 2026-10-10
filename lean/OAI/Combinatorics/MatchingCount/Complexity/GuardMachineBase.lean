import Mathlib
import OAI.Combinatorics.MatchingCount.Model

namespace OAI

namespace MatchingFPRAS.MachineCost
open Turing

def advance {α : Type*} (f : α → Option α) (x : α) : α := (f x).getD x
def run {α : Type*} (f : α → Option α) : ℕ → α → α
  | 0,x => x
  | n+1,x => run f n (advance f x)

lemma run_add {α : Type*} (f : α → Option α) (n m : ℕ) (x : α) :
    run f (n+m) x=run f m (run f n x) := by
  induction n generalizing x with
  | zero => simp only [Nat.zero_add,run]
  | succ n ih => simpa only [Nat.succ_add,run] using ih (advance f x)

lemma run_step_eq {α : Type*} (f : α → Option α) {x y : α}
    (h : advance f x=advance f y) {n : ℕ} (hn : 0<n) : run f n x=run f n y := by
  cases n with
  | zero => omega
  | succ n => simp only [run,h]

def statementCost {Γ Λ σ : Type*} : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => statementCost q+1
  | .write _ q => statementCost q+1
  | .load _ q => statementCost q
  | .branch _ q r => max (statementCost q) (statementCost r)
  | .goto _ => 1
  | .halt => 1
lemma statementCost_pos {Γ Λ σ : Type*} (q : TM1.Stmt Γ Λ σ) : 0<statementCost q := by
  induction q with
  | move _ q ih => simp only [statementCost]; omega
  | write _ q ih => simp only [statementCost]; omega
  | load _ q ih => exact ih
  | branch _ q r ihq ihr => exact lt_of_lt_of_le ihq (le_max_left _ _)
  | goto _ => exact Nat.zero_lt_one
  | halt => exact Nat.zero_lt_one

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ)

theorem statement_translation_time (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    ∃ k, 0 < k ∧ k ≤ statementCost q ∧
      run (TM0.step (TM1to0.tr M)) k ⟨(some q,v),T⟩ =
        TM1to0.trCfg M (TM1.stepAux q v T) := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨k,hk,hc,he⟩ := ih v (T.move d)
    refine ⟨k+1,by omega,by simpa only [statementCost] using Nat.add_le_add_right hc 1,?_⟩
    simpa only [run,advance,TM0.step,TM1to0.tr,TM1to0.trAux,Option.map_some,
      Option.getD_some,TM1.stepAux] using he
  | write a q ih =>
    obtain ⟨k,hk,hc,he⟩ := ih v (T.write (a T.head v))
    refine ⟨k+1,by omega,by simpa only [statementCost] using Nat.add_le_add_right hc 1,?_⟩
    simpa only [run,advance,TM0.step,TM1to0.tr,TM1to0.trAux,Option.map_some,
      Option.getD_some,TM1.stepAux] using he
  | load a q ih =>
    obtain ⟨k,hk,hc,he⟩ := ih (a T.head v) T
    refine ⟨k,hk,hc,?_⟩
    rw [run_step_eq (TM0.step (TM1to0.tr M)) (x:=⟨(some (.load a q),v),T⟩)
      (y:=⟨(some q,a T.head v),T⟩) rfl hk]
    exact he
  | branch p q r ihq ihr =>
    cases hp : p T.head v with
    | false =>
      obtain ⟨k,hk,hc,he⟩ := ihr v T
      refine ⟨k,hk,hc.trans (le_max_right _ _),?_⟩
      have hs : advance (TM0.step (TM1to0.tr M)) ⟨(some (.branch p q r),v),T⟩ =
          advance (TM0.step (TM1to0.tr M)) ⟨(some r,v),T⟩ := by
        simp only [advance,TM0.step,TM1to0.tr,TM1to0.trAux,hp,Bool.cond_false,Option.map_some,Option.getD_some]
      rw [run_step_eq _ hs hk]
      simpa only [TM1.stepAux,hp,Bool.cond_false] using he
    | true =>
      obtain ⟨k,hk,hc,he⟩ := ihq v T
      refine ⟨k,hk,hc.trans (le_max_left _ _),?_⟩
      have hs : advance (TM0.step (TM1to0.tr M)) ⟨(some (.branch p q r),v),T⟩ =
          advance (TM0.step (TM1to0.tr M)) ⟨(some q,v),T⟩ := by
        simp only [advance,TM0.step,TM1to0.tr,TM1to0.trAux,hp,Bool.cond_true,Option.map_some,Option.getD_some]
      rw [run_step_eq _ hs hk]
      simpa only [TM1.stepAux,hp,Bool.cond_true] using he
  | goto l =>
    refine ⟨1,by decide,le_rfl,?_⟩
    simp only [run,advance,TM0.step,TM1to0.tr,TM1to0.trAux,Option.map_some,
      Option.getD_some,TM1.stepAux,TM1to0.trCfg,Tape.write_self]
  | halt =>
    refine ⟨1,by decide,le_rfl,?_⟩
    simp only [run,advance,TM0.step,TM1to0.tr,TM1to0.trAux,Option.map_some,
      Option.getD_some,TM1.stepAux,TM1to0.trCfg,Tape.write_self,Option.map_none]

noncomputable def programCost [Fintype Λ] : ℕ := Finset.univ.sup (fun l=>statementCost (M l))
omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
lemma statementCost_le_programCost [Fintype Λ] (l : Λ) :
    statementCost (M l)≤programCost M := Finset.le_sup (f:=fun l=>statementCost (M l)) (Finset.mem_univ l)
omit [Inhabited Γ] [Inhabited σ] in
lemma programCost_pos [Fintype Λ] : 0<programCost M :=
  (statementCost_pos (M default)).trans_le (statementCost_le_programCost M default)

theorem run_translation_time [Fintype Λ] (n : ℕ) (c : TM1.Cfg Γ Λ σ) :
    ∃ k≤programCost M*n,
      run (TM0.step (TM1to0.tr M)) k (TM1to0.trCfg M c)=
        TM1to0.trCfg M (run (TM1.step M) n c) := by
  induction n generalizing c with
  | zero => exact ⟨0,by omega,rfl⟩
  | succ n ih =>
    rcases c with ⟨l,v,T⟩
    cases l with
    | none =>
      have he : run (TM1.step M) (n+1) ⟨none,v,T⟩=⟨none,v,T⟩ := by
        have h : ∀ k, run (TM1.step M) k ⟨none,v,T⟩=⟨none,v,T⟩ := by
          intro k; induction k with
          | zero => simp only [run]
          | succ k ihk => simpa only [run,advance,TM1.step,Option.getD_none] using ihk
        exact h _
      exact ⟨0,by omega,by rw [run,he]⟩
    | some l =>
      obtain ⟨j,hj,hjc,hje⟩ := statement_translation_time M (M l) v T
      obtain ⟨k,hk,hke⟩ := ih (TM1.stepAux (M l) v T)
      refine ⟨j+k,?_,?_⟩
      · have := hjc.trans (statementCost_le_programCost M l)
        simpa only [Nat.mul_succ] using Nat.add_le_add this hk |>.trans_eq (Nat.add_comm _ _)
      · rw [run_add]
        change run (TM0.step (TM1to0.tr M)) k
          (run (TM0.step (TM1to0.tr M)) j ⟨(some (M l),v),T⟩)=_
        rw [hje,hke]
        rfl
end MatchingFPRAS.MachineCost

namespace MatchingFPRAS.PostCompiler
open Turing MachineCost
open scoped Classical

variable {Λ : Type*} [Inhabited Λ]
variable (M : Λ → Symbol → Option (Λ × TM0.Stmt Symbol)) (S : Finset Λ) (hS : TM0.Supports M (S : Set Λ))

noncomputable def index : S ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
noncomputable def pack (q : S) : Fin (S.card+1) := (index S q).succ
noncomputable def unpack (i : Fin (S.card+1)) : S :=
  if h : i.val=0 then ⟨default,hS.1⟩ else
    (index S).symm ⟨i.val-1,by have := i.isLt; omega⟩
lemma unpack_pack (q : S) : unpack M S hS (pack S q)=q := by
  simp [unpack,pack]
omit [Inhabited Λ] in
lemma pack_ne_zero (q : S) : pack S q≠0 := by simp [pack]

noncomputable def packState (q : Λ) : Fin (S.card+1) :=
  if h : q∈S then pack S ⟨q,h⟩ else 0
omit [Inhabited Λ] in
lemma packState_of_mem (q : Λ) (hq : q∈S) : packState S q=pack S ⟨q,hq⟩ := by
  simp [packState,hq]

noncomputable def sealedMachine : RandomMachine where
  states := S.card
  transition i a _ := if i=0 then some (pack S ⟨default,hS.1⟩,.write a) else
    (M (unpack M S hS i).val a).map (fun (q,s)=>(packState S q,s))

abbrev Phase (Λ : Type*) := TM0.Cfg Symbol Λ × Bool

def perform (s : TM0.Stmt Symbol) (T : Tape Symbol) : Tape Symbol := match s with
  | .move d => T.move d
  | .write a => T.write a

noncomputable def phaseStep (x : Phase Λ) : Phase Λ :=
  if x.2 then
    match M x.1.q x.1.Tape.head with
    | none => (x.1,false)
    | some (q,s) => (⟨q,perform s x.1.Tape⟩,true)
  else x

def well (x : Phase Λ) : Prop := x.1.q∈S ∧ (x.2=false → TM0.step M x.1=none)
noncomputable def embed (x : Phase Λ) : Configuration (sealedMachine M S hS) :=
  ⟨if x.2 then some (packState S x.1.q) else none,x.1.Tape⟩

include hS

lemma phaseStep_well (x : Phase Λ) (hx : well M S x) : well M S (phaseStep M x) := by
  rcases x with ⟨⟨q,T⟩,b⟩
  cases b with
  | false => exact hx
  | true =>
    cases he : M q T.head with
    | none => simpa [well,phaseStep,he,TM0.step] using hx.1
    | some ys =>
      rcases ys with ⟨y,s⟩
      simpa [well,phaseStep,he] using hS.2 he hx.1

omit hS in
lemma phaseStep_first (_hS : TM0.Supports M (S : Set Λ)) (x : Phase Λ) (hx : well M S x) :
    (phaseStep M x).1=advance (TM0.step M) x.1 := by
  rcases x with ⟨⟨q,T⟩,b⟩
  cases b with
  | false => simp [phaseStep,advance,hx.2 rfl]
  | true =>
    cases he : M q T.head with
    | none => simp [phaseStep,advance,TM0.step,he]
    | some ys => rcases ys with ⟨y,s⟩; cases s <;> simp [phaseStep,advance,TM0.step,he,perform]

lemma embed_step (x : Phase Λ) (hx : well M S x) (b : Bool) :
    tick (sealedMachine M S hS) (embed M S hS x) b=embed M S hS (phaseStep M x) := by
  rcases x with ⟨⟨q,T⟩,live⟩
  cases live with
  | false => rfl
  | true =>
    have hp := pack_ne_zero S (⟨q,hx.1⟩ : S)
    cases he : M q T.head with
    | none => simp [embed,tick,sealedMachine,phaseStep,packState_of_mem S q hx.1,hp,unpack_pack,he]
    | some ys =>
      rcases ys with ⟨y,s⟩
      cases s <;> simp [embed,tick,sealedMachine,phaseStep,packState_of_mem S q hx.1,hp,unpack_pack,he,perform]

lemma phaseRun (n : ℕ) (x : Phase Λ) (hx : well M S x) :
    well M S ((phaseStep M)^[n] x) ∧
      ((phaseStep M)^[n] x).1=MachineCost.run (TM0.step M) n x.1 := by
  induction n generalizing x with
  | zero => exact ⟨hx,rfl⟩
  | succ n ih =>
    have h := ih (phaseStep M x) (phaseStep_well M S hS x hx)
    rw [Function.iterate_succ_apply]
    exact ⟨h.1,by rw [h.2,phaseStep_first M S hS x hx]; rfl⟩

lemma phaseRun_stops (n : ℕ) (x : Phase Λ) (hx : well M S x)
    (hh : TM0.step M (MachineCost.run (TM0.step M) n x.1)=none) :
    ((phaseStep M)^[n+1] x).2=false ∧
      ((phaseStep M)^[n+1] x).1=MachineCost.run (TM0.step M) n x.1 := by
  obtain ⟨hw,he⟩ := phaseRun M S hS n x hx
  rw [Function.iterate_succ_apply']
  rw [←he] at hh ⊢
  generalize (phaseStep M)^[n] x=y at *
  rcases y with ⟨⟨q,T⟩,live⟩
  have hq0 : M q T.head=none := Option.map_eq_none_iff.mp hh
  cases live <;> simp [phaseStep,hq0]

lemma embed_fold (bits : List Bool) (x : Phase Λ) (hx : well M S x) :
    bits.foldl (tick (sealedMachine M S hS)) (embed M S hS x)=
      embed M S hS ((phaseStep M)^[bits.length] x) := by
  induction bits generalizing x with
  | nil => rfl
  | cons b bits ih =>
    rw [List.foldl_cons,embed_step M S hS x hx,ih _ (phaseStep_well M S hS x hx),
      List.length_cons,Function.iterate_succ_apply]

lemma entry (a : Symbol) (b : Bool) :
    (sealedMachine M S hS).transition 0 a b=some (pack S ⟨default,hS.1⟩,.write a) := by
  dsimp only [sealedMachine]
  split
  · rfl
  · rename_i h; exact False.elim (h rfl)

lemma initial_tick (input : List Symbol) (b : Bool) :
    tick (sealedMachine M S hS) (initial (sealedMachine M S hS) input) b=
      embed M S hS (TM0.init input,true) := by
  simp only [tick,initial,entry,Tape.write_self,embed,TM0.init,packState_of_mem S default hS.1,
    ↓reduceIte]

omit hS in
lemma halted_tick (A : RandomMachine) (c : Configuration A) (h : c.state=none) (b : Bool) : tick A c b=c := by
  rcases c with ⟨s,T⟩
  change s=none at h
  subst s
  rfl
omit hS in
lemma halted_fold (A : RandomMachine) (c : Configuration A) (h : c.state=none) (bits : List Bool) :
    bits.foldl (tick A) c=c := by
  induction bits with
  | nil => rfl
  | cons b bits ih => rw [List.foldl_cons,halted_tick A c h b,ih]

theorem seal_words (input output : List Symbol) (n : ℕ)
    (hhalt : TM0.step M (MachineCost.run (TM0.step M) n (TM0.init input))=none)
    (hout : (MachineCost.run (TM0.step M) n (TM0.init input)).Tape.right₀=
      ListBlank.mk output) (bits : Fin (n+2) → Bool) :
    (MatchingFPRAS.run (sealedMachine M S hS) input bits).state=none ∧
      (MatchingFPRAS.run (sealedMachine M S hS) input bits).tape.right₀=ListBlank.mk output := by
  let x : Phase Λ := (TM0.init input,true)
  have hx : well M S x := ⟨hS.1,by intro h; cases h⟩
  obtain ⟨hs,he⟩ := phaseRun_stops M S hS n x hx hhalt
  have hr : MatchingFPRAS.run (sealedMachine M S hS) input bits=embed M S hS ((phaseStep M)^[n+1] x) := by
    unfold MatchingFPRAS.run
    rw [List.ofFn_succ,List.foldl_cons,initial_tick,embed_fold M S hS _ x hx,List.length_ofFn]
  constructor
  · rw [hr]
    simp only [embed,hs,Bool.false_eq_true,↓reduceIte]
  · rw [hr]
    change ((phaseStep M)^[n+1] x).1.Tape.right₀=_
    rw [he]
    exact hout

theorem seal_outputs (input : List Symbol) (n : ℕ) (q : ℚ)
    (hhalt : TM0.step M (MachineCost.run (TM0.step M) n (TM0.init input))=none)
    (hout : (MachineCost.run (TM0.step M) n (TM0.init input)).Tape.right₀=
      ListBlank.mk (encodeRat q)) (bits : Fin (n+2) → Bool) :
    Outputs (sealedMachine M S hS) input bits q := by
  let x : Phase Λ := (TM0.init input,true)
  have hx : well M S x := ⟨hS.1,by intro h; cases h⟩
  obtain ⟨hs,he⟩ := phaseRun_stops M S hS n x hx hhalt
  have hr : MatchingFPRAS.run (sealedMachine M S hS) input bits=embed M S hS ((phaseStep M)^[n+1] x) := by
    unfold MatchingFPRAS.run
    rw [List.ofFn_succ,List.foldl_cons,initial_tick,embed_fold M S hS _ x hx,List.length_ofFn]
  constructor
  · rw [hr]
    simp only [embed,hs,Bool.false_eq_true,↓reduceIte]
  · rw [hr]
    change ((phaseStep M)^[n+1] x).1.Tape.right₀=_
    rw [he]
    exact hout

omit hS

open Turing MachineCost
open scoped Classical

theorem outputs_extend (A : RandomMachine) (input : List Symbol) (q : ℚ)
    {n t : ℕ} (hnt : n ≤ t) (bits : Fin t → Bool)
    (h : Outputs A input (fun i : Fin n=>bits (Fin.castLE hnt i)) q) :
    Outputs A input bits q := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hnt
  have hr : MatchingFPRAS.run A input bits=
      MatchingFPRAS.run A input (fun i : Fin n=>bits (Fin.castLE hnt i)) := by
    unfold MatchingFPRAS.run
    rw [List.ofFn_add,List.foldl_append]
    exact halted_fold A _ h.1 _
  constructor
  · rw [hr]; exact h.1
  · rw [hr]; exact h.2

theorem words_extend (A : RandomMachine) (input output : List Symbol)
    {n t : ℕ} (hnt : n ≤ t) (bits : Fin t → Bool)
    (h : (MatchingFPRAS.run A input (fun i : Fin n=>bits (Fin.castLE hnt i))).state=none ∧
      (MatchingFPRAS.run A input (fun i : Fin n=>bits (Fin.castLE hnt i))).tape.right₀=ListBlank.mk output) :
    (MatchingFPRAS.run A input bits).state=none ∧
      (MatchingFPRAS.run A input bits).tape.right₀=ListBlank.mk output := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hnt
  have hr : MatchingFPRAS.run A input bits=
      MatchingFPRAS.run A input (fun i : Fin n=>bits (Fin.castLE hnt i)) := by
    unfold MatchingFPRAS.run
    rw [List.ofFn_add,List.foldl_append]
    exact halted_fold A _ h.1 _
  rw [hr]
  exact h

variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ] [Fintype Λ] [Fintype σ]
variable (M : Λ → TM1.Stmt Symbol Λ σ)

omit [Inhabited σ] [Fintype σ] in
lemma finite_supported : TM1.Supports M Finset.univ := by
  constructor
  · exact Finset.mem_univ _
  · intro l hl
    induction M l with
    | move _ q ih => exact ih
    | write _ q ih => exact ih
    | load _ q ih => exact ih
    | branch _ q r ihq ihr => exact ⟨ihq,ihr⟩
    | goto _ => exact fun _ _=>Finset.mem_univ _
    | halt => trivial

noncomputable def compiled : RandomMachine :=
  sealedMachine (TM1to0.tr M) (TM1to0.trStmts M Finset.univ)
    (TM1to0.tr_supports M (finite_supported M))

theorem compiled_outputs (input : List Symbol) (n t : ℕ) (q : ℚ)
    (hhalt : (MachineCost.run (TM1.step M) n (TM1.init input)).l=none)
    (hout : (MachineCost.run (TM1.step M) n (TM1.init input)).Tape.right₀=
      ListBlank.mk (encodeRat q))
    (ht : programCost M*n+2 ≤ t) (bits : Fin t → Bool) : Outputs (compiled M) input bits q := by
  obtain ⟨k,hk,he⟩ := run_translation_time M n (TM1.init input)
  have hi : TM1to0.trCfg M (TM1.init input)=TM0.init input := rfl
  rw [hi] at he
  have hh : TM0.step (TM1to0.tr M)
      (MachineCost.run (TM0.step (TM1to0.tr M)) k (TM0.init input))=none := by
    rw [he]
    generalize hc : MachineCost.run (TM1.step M) n (TM1.init input)=c at hhalt ⊢
    rcases c with ⟨l,v,T⟩
    change l=none at hhalt
    subst l
    rfl
  have ho : (MachineCost.run (TM0.step (TM1to0.tr M)) k (TM0.init input)).Tape.right₀=
      ListBlank.mk (encodeRat q) := by
    rw [he]
    exact hout
  have hkt : k+2 ≤ t := (Nat.add_le_add_right hk 2).trans ht
  exact outputs_extend (compiled M) input q hkt bits
    (seal_outputs (TM1to0.tr M) (TM1to0.trStmts M Finset.univ)
      (TM1to0.tr_supports M (finite_supported M)) input k q hh ho _)

theorem compiled_words (input output : List Symbol) (n t : ℕ)
    (hhalt : (MachineCost.run (TM1.step M) n (TM1.init input)).l=none)
    (hout : (MachineCost.run (TM1.step M) n (TM1.init input)).Tape.right₀=
      ListBlank.mk output)
    (ht : programCost M*n+2 ≤ t) (bits : Fin t → Bool) :
    (MatchingFPRAS.run (compiled M) input bits).state=none ∧
      (MatchingFPRAS.run (compiled M) input bits).tape.right₀=ListBlank.mk output := by
  obtain ⟨k,hk,he⟩ := run_translation_time M n (TM1.init input)
  have hi : TM1to0.trCfg M (TM1.init input)=TM0.init input := rfl
  rw [hi] at he
  have hh : TM0.step (TM1to0.tr M)
      (MachineCost.run (TM0.step (TM1to0.tr M)) k (TM0.init input))=none := by
    rw [he]
    generalize hc : MachineCost.run (TM1.step M) n (TM1.init input)=c at hhalt ⊢
    rcases c with ⟨l,v,T⟩
    change l=none at hhalt
    subst l
    rfl
  have ho : (MachineCost.run (TM0.step (TM1to0.tr M)) k (TM0.init input)).Tape.right₀=
      ListBlank.mk output := by
    rw [he]
    exact hout
  have hkt : k+2 ≤ t := (Nat.add_le_add_right hk 2).trans ht
  exact words_extend (compiled M) input output hkt bits
    (seal_words (TM1to0.tr M) (TM1to0.trStmts M Finset.univ)
      (TM1to0.tr_supports M (finite_supported M)) input output k hh ho _)
end MatchingFPRAS.PostCompiler

end OAI
