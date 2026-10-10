import Mathlib
import OAI.Computability.MinUncut.Graphs.SelectedGraphEndpoint
import OAI.Computability.MinUncut.Encoding.DecodedGraphCore

namespace OAI

section
noncomputable section
namespace MinUncut.Uniform
open MinUncut.Preprocess MinUncut.Costed MinUncut.Costed.Arena
open _root_.Turing _root_.OAI.Turing Turing.ToPartrec _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Polynomial
open MinUncutGames MinUncutGames.BinaryEncoding MinUncutGames.Foundations.Complexity

attribute [local irreducible] selectedInner selectedOuter program

lemma initializer_exists : ∃c : Code,∀K,∃p : Polynomial ℕ,∀xs n table k junk,
    (MinUncut.Costed.SourceWords.completeGraphWords (selectedParameters K) (chosenEnumeration K)
      (chosenRepetition K) (chosenNoise K)) xs=n::((table : List Bool).map Bool.toNat++2::k::junk) →
    Nonempty (TM2OutputsInTime (initializedGraphMachine c)
      (trList (K::(encodeWords xs).map FrameDecode.symbol))
      (some (nameBits n++table++nameBits k)) (p.eval (encodeWords xs).length)) :=
  by
    have hh := exists_graph_initializer program program_computable
    exact hh

def initializerCode : Code := Classical.choose initializer_exists
def initializerTime (K : ℕ) : Polynomial ℕ := Classical.choose (Classical.choose_spec initializer_exists K)
def initializer_outputs (K : ℕ) (F : BinaryFormula.Formula) :
    TM2OutputsInTime (initializedGraphMachine initializerCode)
      (trList (K::(formulaBits (frontend F).val).map FrameDecode.symbol))
      (some (output K F).bits) ((initializerTime K).eval (formulaBits (frontend F).val).length) := by
  apply Classical.choice
  obtain ⟨table,junk,hj,hbits⟩:=output_words K F
  have hh:=Classical.choose_spec (Classical.choose_spec initializer_exists K)
    (formulaWords (frontend F).val) (output K F).vertices table (output K F).threshold junk hj
  rw [←hbits] at hh
  exact hh

attribute [local irreducible] frontend output initializerCode initializerTime

def coreMachine : FinTM2 :=
  decodedMachine initializerCode
lemma core_finite (k : coreMachine.K) : Finite (coreMachine.Γ k) :=
  decodedMachine_finite _ k

def coreTime (K : ℕ) : Polynomial ℕ :=
  initializerTime K+C (2*(nameBits K).length+3*(K+1)+4)+C 11*X

def core_outputs (K : ℕ) (F : BinaryFormula.Formula) :
    TM2OutputsInTime coreMachine (nameBits K++formulaBits (frontend F).val)
      (some (output K F).bits) ((coreTime K).eval (formulaBits (frontend F).val).length) := by
  have hh:=decoded_outputs initializerCode K (formulaBits (frontend F).val) (output K F).bits
    ((initializerTime K).eval (formulaBits (frontend F).val).length) (initializer_outputs K F)
  refine ⟨hh.toEvalsTo,hh.steps_le_m.trans ?_⟩
  simp only [coreTime,eval_add,eval_C,eval_mul,eval_X]
  omega
end MinUncut.Uniform

end
end
section
noncomputable section
namespace MinUncut.Costed.Framed
open _root_.Turing _root_.OAI.Turing MinUncutGames.Foundations.Complexity
variable (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)
abbrev Tape := M.K ⊕ Unit
abbrev Alphabet : Tape M → Type := MachineEmbedding.Alphabet M.Γ (fun _ : Unit=>Bool)
abbrev Label := M.Λ ⊕ Option Bool
abbrev State := M.σ × Option Bool

def extra : Option Bool → TM2.Stmt (Alphabet M) (Label M) (State M)
  | none => .pop (.inl M.k₀) (fun s a=>(s.1,a.map ei))
      (.push (.inr ()) (fun s=>s.2.getD false)
        (.branch (fun s=>s.2.getD false)
          (.load (fun s=>(s.1,none)) (.goto fun _=>.inr (some false)))
          (.load (fun s=>(s.1,none)) (.goto fun _=>.inl M.main))))
  | some false => .pop (.inl M.k₀) (fun s a=>(s.1,a.map ei))
      (.push (.inr ()) (fun s=>s.2.getD false)
        (.load (fun s=>(s.1,none)) (.goto fun _=>.inr none)))
  | some true => .pop (.inr ()) (fun s a=>(s.1,a))
      (.branch (fun s=>s.2.isSome)
        (.push (.inl M.k₁) (fun s=>eo.symm (s.2.getD false))
          (.load (fun s=>(s.1,none)) (.goto fun _=>.inr (some true))))
        (.load (fun s=>(s.1,none)) .halt))
def program : Label M → TM2.Stmt (Alphabet M) (Label M) (State M) :=
  MachineEmbedding.program (some (.inr (some true))) M.m (extra M ei eo)
def machine : FinTM2 where
  K := Tape M
  kFin := by letI:=M.kFin; exact inferInstanceAs (Fintype (M.K ⊕ Unit))
  k₀ := .inl M.k₀
  k₁ := .inl M.k₁
  Γ := Alphabet M
  Γk₀Fin := M.Γk₀Fin
  Λ := Label M
  ΛFin := by letI:=M.ΛFin; exact inferInstanceAs (Fintype (M.Λ ⊕ Option Bool))
  main := .inr none
  σ := State M
  σFin := by letI:=M.σFin; exact inferInstanceAs (Fintype (M.σ × Option Bool))
  initialState := (M.initialState,none)
  m := program M ei eo
lemma finiteAlphabet (hm : MachineFiniteAlphabet.FiniteAlphabet M)
    (k : (machine M ei eo).K) : Finite ((machine M ei eo).Γ k) := by
  cases k with
  | inl k => exact hm k
  | inr k => exact inferInstanceAs (Finite Bool)

def readTapes (v acc : List Bool) : ∀k,List (Alphabet M k) :=
  MachineEmbedding.tapes (initList M (v.map ei.symm)).stk (fun _=>acc)
def readCfg (label : Option Bool) (v acc : List Bool) : (machine M ei eo).Cfg :=
  ⟨some (.inr label),(M.initialState,none),readTapes M ei v acc⟩
def embedded (acc : List Bool) (c : M.Cfg) : (machine M ei eo).Cfg :=
  MachineEmbedding.configuration (some (.inr (some true))) none (fun _ : Unit=>acc) c
lemma read_input (v acc : List Bool) : (readTapes M ei v acc) (.inl M.k₀)=v.map ei.symm := by
  simp [readTapes,initList]
lemma read_extra (v acc : List Bool) : (readTapes M ei v acc) (.inr ())=acc := rfl
lemma read_put_input (v acc w : List Bool) :
    Function.update (readTapes M ei v acc) (.inl M.k₀) (w.map ei.symm)=readTapes M ei w acc := by
  funext k
  cases k with
  | inl k =>
    by_cases h:k=M.k₀
    · subst k; simp [readTapes,initList]
    · simp [readTapes,initList,Function.update,h]
  | inr k => simp [readTapes,Function.update]
lemma read_put_extra (v acc w : List Bool) :
    Function.update (readTapes M ei v acc) (.inr ()) w=readTapes M ei v w := by
  funext k
  cases k with
  | inl k => simp [readTapes,Function.update]
  | inr k => cases k; simp [readTapes]
lemma read_step (b : Bool) (v acc : List Bool) :
    (machine M ei eo).step (readCfg M ei eo none (b::v) acc)=
      some (if b then readCfg M ei eo (some false) v (b::acc)
        else embedded M ei eo (b::acc) (initList M (v.map ei.symm))) := by
  change some (TM2.stepAux (extra M ei eo none) (M.initialState,none) (readTapes M ei (b::v) acc))=_
  cases b <;> simp only [extra,TM2.stepAux,read_input,List.map_cons,List.head?_cons,Option.map_some,
    Equiv.apply_symm_apply,Option.getD_some,List.tail_cons,
    Bool.cond_false,Bool.cond_true,Bool.false_eq_true,ite_false,ite_true]
  all_goals
    congr 2
    funext k
    cases k with
    | inl k =>
      by_cases h:k=M.k₀
      · subst k; simp [readTapes,initList]
      · simp [readTapes,initList,Function.update,h]
    | inr k => cases k; simp [readTapes,Function.update]
lemma payload_step (b : Bool) (v acc : List Bool) :
    (machine M ei eo).step (readCfg M ei eo (some false) (b::v) acc)=
      some (readCfg M ei eo none v (b::acc)) := by
  change some (TM2.stepAux (extra M ei eo (some false)) (M.initialState,none) (readTapes M ei (b::v) acc))=_
  simp only [extra,TM2.stepAux,read_input,List.map_cons,List.head?_cons,Option.map_some,
    Equiv.apply_symm_apply,Option.getD_some,List.tail_cons]
  congr 2
  funext k
  cases k with
  | inl k =>
    by_cases h:k=M.k₀
    · subst k; simp [readTapes,initList]
    · simp [readTapes,initList,Function.update,h]
  | inr k => cases k; simp [readTapes,Function.update]
open MinUncutGames.BinaryEncoding
lemma read_frames (bits v acc : List Bool) :
    Steps (machine M ei eo).step (frame bits).length
      (readCfg M ei eo none (frame bits++v) acc)
      (embedded M ei eo ((frame bits).reverse++acc) (initList M (v.map ei.symm))) := by
  induction bits generalizing acc with
  | nil => exact steps_one (read_step M ei eo false v acc)
  | cons b bits ih =>
    have h1 := steps_one (read_step M ei eo true (b::(frame bits++v)) acc)
    have h2 := steps_one (payload_step M ei eo b (frame bits++v) (true::acc))
    have hh := steps_trans (steps_trans h1 h2) (ih (b::true::acc))
    simpa only [frame,List.cons_append,List.length_cons,List.reverse_cons,List.append_assoc,
      List.singleton_append,List.nil_append,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh
lemma read_init (v : List Bool) :
    readCfg M ei eo none v []=initList (machine M ei eo) (v.map ei.symm) := by
  change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases h:k=M.k₀ <;> simp [readTapes,initList,h,machine]
    rfl
  | inr k => simp [readTapes,initList,machine]
lemma finish_step (b : Bool) (w acc : List Bool) :
    (machine M ei eo).step (embedded M ei eo (b::acc) (haltList M (w.map eo.symm)))=
      some (embedded M ei eo acc (haltList M ((b::w).map eo.symm))) := by
  change some (TM2.stepAux (extra M ei eo (some true)) (M.initialState,none)
    (MachineEmbedding.tapes (haltList M (w.map eo.symm)).stk (fun _ : Unit=>b::acc)))=_
  simp only [extra,TM2.stepAux,MachineEmbedding.tapes_inr,List.head?_cons,List.tail_cons,
    Option.isSome_some,Bool.cond_true,Option.getD_some]
  congr 2
  funext k
  cases k with
  | inl k =>
    by_cases h:k=M.k₁
    · subst k; simp [haltList,Function.update]
    · simp [haltList,Function.update,h]
  | inr k => cases k; simp [haltList,Function.update]
lemma finish_empty (w : List Bool) :
    (machine M ei eo).step (embedded M ei eo [] (haltList M (w.map eo.symm)))=
      some (haltList (machine M ei eo) (w.map eo.symm)) := by
  change some (TM2.stepAux (extra M ei eo (some true)) (M.initialState,none)
    (MachineEmbedding.tapes (haltList M (w.map eo.symm)).stk (fun _ : Unit=>[])))=_
  simp only [extra,TM2.stepAux,MachineEmbedding.tapes_inr,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false]
  congr 2
  funext k
  cases k with
  | inl k =>
    by_cases h:k=M.k₁
    · subst k
      simp [haltList,Function.update,machine]
      rfl
    · simp [haltList,Function.update,h,machine]
  | inr k => cases k; simp [Function.update,machine]
lemma finish_steps (w acc : List Bool) :
    Steps (machine M ei eo).step (acc.length+1)
      (embedded M ei eo acc (haltList M (w.map eo.symm)))
      (haltList (machine M ei eo) ((acc.reverse++w).map eo.symm)) := by
  induction acc generalizing w with
  | nil => exact steps_one (finish_empty M ei eo w)
  | cons b acc ih =>
    have hh:=steps_head (finish_step M ei eo b w acc) (ih (b::w))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

def execute (K : ℕ) (v w : List Bool) (B : ℕ)
    (h : TM2OutputsInTime M (v.map ei.symm) (some (w.map eo.symm)) B) :
    TM2OutputsInTime (machine M ei eo) ((nameBits K++v).map ei.symm)
      (some ((nameBits K++w).map eo.symm)) (B+2*(nameBits K).length+1) := by
  have hr := steps_timed (read_frames M ei eo K.bits v []) le_rfl
  simp only [List.append_nil,read_init] at hr
  let hm := MachineComposition.embeddedExecution (some (.inr (some true))) none
    (fun _ : Unit=>(nameBits K).reverse) M.m (extra M ei eo) h
  have hf := steps_timed (finish_steps M ei eo w (nameBits K).reverse) le_rfl
  simp only [List.length_reverse,List.reverse_reverse] at hf
  let hh := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hr hm
  let hh' := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hh hf
  exact ⟨hh'.toEvalsTo,by have hb:=hh'.steps_le_m; change _≤B+2*(nameBits K).length+1; simp only [nameBits] at hb ⊢; omega⟩
end MinUncut.Costed.Framed

end
end

end OAI
