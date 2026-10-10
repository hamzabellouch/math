import OAI.NumberTheory.SingleFold.TuringSimulation

namespace OAI

noncomputable section

namespace SingleFold.TM2Macro
open Turing Turing.PartrecToTM2 StateTransition Relation
open scoped Classical
variable {n : ℕ} {Λ : Type}
def Good (A : Finset (Stmt Λ)) : Label n Λ → Prop
  | .code q _=>q∈A | .restore _ _ q _=>q∈A
  | .start _=>True | .divide _=>True | .bit _=>True | .pushBit _ _=>True
  | .reverse _=>True | .pushRev _ _=>True
inductive BLabel (n : ℕ) (C : Type)
  | code (q : C) (v : Store)
  | restore (k : Stack) (d : Fin 5) (q : C) (v : Store)
  | start (i : Fin (n+1))
  | divide (i : Fin n)
  | bit (i : Fin n)
  | pushBit (i : Fin n) (d : Fin 5)
  | reverse (i : Fin n)
  | pushRev (i : Fin n) (d : Fin 5)
  deriving Fintype
def forget (A : Finset (Stmt Λ)) : BLabel n {q // q∈A} → Label n Λ
  | .code q v=>.code q.val v | .restore k d q v=>.restore k d q.val v
  | .start i=>.start i | .divide i=>.divide i | .bit i=>.bit i | .pushBit i d=>.pushBit i d
  | .reverse i=>.reverse i | .pushRev i d=>.pushRev i d
lemma forget_good (A : Finset (Stmt Λ)) (q : BLabel n {q // q∈A}) : Good A (forget A q) := by
  cases q <;> simp only [forget,Good]
  all_goals exact Subtype.property _
lemma forget_surj (A : Finset (Stmt Λ)) (q : {q : Label n Λ // Good A q}) :
    ∃ b : BLabel n {q // q∈A}, forget A b=q.val := by
  rcases q with ⟨q,hq⟩
  cases q with
  | code q v => exact ⟨.code ⟨q,hq⟩ v,rfl⟩
  | restore k d q v => exact ⟨.restore k d ⟨q,hq⟩ v,rfl⟩
  | start i => exact ⟨.start i,rfl⟩
  | divide i => exact ⟨.divide i,rfl⟩
  | bit i => exact ⟨.bit i,rfl⟩
  | pushBit i d => exact ⟨.pushBit i d,rfl⟩
  | reverse i => exact ⟨.reverse i,rfl⟩
  | pushRev i d => exact ⟨.pushRev i d,rfl⟩
instance finite_good (A : Finset (Stmt Λ)) : Finite {q : Label n Λ // Good A q} :=
  Finite.of_surjective (fun b=>⟨forget A b,forget_good A b⟩) (fun q=>by
    obtain ⟨b,hb⟩:=forget_surj A q
    exact ⟨b,Subtype.ext hb⟩)
lemma program_within (M : Λ → Stmt Λ) (initial : Λ) (A : Finset (Stmt Λ))
    (hinit : M initial∈A) (hsub : ∀ q∈A,TM2.stmts₁ q⊆A)
    (hgoto : ∀ f, (TM2.Stmt.goto f : Stmt Λ)∈A → ∀ v,M (f v)∈A) :
    ∀ q : Label n Λ,Good A q → (program M initial q).Within (Good A) := by
  intro q hq
  cases q with
  | code q v =>
    change q∈A at hq
    have hs := hsub q hq
    cases q with
    | push k f q => exact hs (by simp [TM2.stmts₁,TM2.stmts₁_self])
    | peek k f q => intro d; exact hs (by simp [TM2.stmts₁,TM2.stmts₁_self])
    | pop k f q => intro d; exact hs (by simp [TM2.stmts₁,TM2.stmts₁_self])
    | load f q => exact hs (by simp [TM2.stmts₁,TM2.stmts₁_self])
    | branch f q r =>
      change (if f v then q else r)∈A
      split <;> exact hs (by simp [TM2.stmts₁,TM2.stmts₁_self])
    | goto f => exact hgoto f hq v
    | halt => trivial
  | restore k d q v => dsimp only [program]; split <;> exact hq
  | start i => simp only [program]; split <;> simp_all [Macro.Instr.Within,Good]
  | divide i => exact ⟨trivial,trivial⟩
  | bit i => intro d; trivial
  | pushBit i d => trivial
  | reverse i => intro d; change Good A (if d.val=0 then _ else _); split <;> trivial
  | pushRev i d => trivial

def statements (M : Λ → Stmt Λ) (S : Finset Λ) : Finset (Stmt Λ) := S.biUnion (fun l=>TM2.stmts₁ (M l))
lemma statements_self (M : Λ → Stmt Λ) (S : Finset Λ) {l : Λ} (hl : l∈S) : M l∈statements M S :=
  Finset.mem_biUnion.mpr ⟨l,hl,TM2.stmts₁_self⟩
lemma statements_sub (M : Λ → Stmt Λ) (S : Finset Λ) (q : Stmt Λ) (hq : q∈statements M S) :
    TM2.stmts₁ q⊆statements M S := by
  obtain ⟨l,hl,hq⟩:=Finset.mem_biUnion.mp hq
  intro r hr
  exact Finset.mem_biUnion.mpr ⟨l,hl,TM2.stmts₁_trans hq hr⟩
lemma statements_goto (M : Λ → Stmt Λ) (S : Finset Λ) (hS : ∀ l∈S,TM2.SupportsStmt S (M l))
    (f : Store → Λ) (hf : (TM2.Stmt.goto f : Stmt Λ)∈statements M S) (v : Store) :
    M (f v)∈statements M S := by
  obtain ⟨l,hl,hf⟩:=Finset.mem_biUnion.mp hf
  exact statements_self M S (TM2.stmts₁_supportsStmt_mono hf (hS l hl) v)

instance fintype_good (A : Finset (Stmt Λ)) : Fintype {q : Label n Λ // Good A q} := Fintype.ofFinite _
abbrev FiniteState (n : ℕ) (M : Λ → Stmt Λ) (S : Finset Λ) := {q : Label n Λ // Good (statements M S) q}
def finStart (M : Λ → Stmt Λ) (S : Finset Λ) : FiniteState n M S := ⟨.start (Fin.last n),trivial⟩
def finProgram (M : Λ → Stmt Λ) (initial : Λ) (S : Finset Λ) : FiniteState n M S → Macro.Instr (FiniteState n M S) (Reg n) :=
  Macro.restrict (program M initial) (Good (statements M S)) (finStart M S)
def counterProgram (M : Λ → Stmt Λ) (initial : Λ) (S : Finset Λ) : Counter.Machine (Macro.State (FiniteState n M S)) (Macro.Reg (Reg n)) :=
  Macro.compile (finProgram M initial S) (finStart M S)
def inputSlot : Macro.Reg (Reg n) → Option (Fin n)
  | .inl (.inr i)=>some i | _=>none
def counterInput (a : Fin n → ℕ) : Macro.Reg (Reg n) → ℕ := fun j=>(inputSlot j).elim 0 a
lemma counterInput_eq (a : Fin n → ℕ) : counterInput a=Sum.elim (initValues [] [] a) (fun b=>if b then 0 else 0) := by
  funext j
  rcases j with (k|i)|b
  · cases k <;> rfl
  · rfl
  · cases b <;> rfl
lemma counter_halts (M : Λ → Stmt Λ) (initial : Λ) (S : Finset Λ)
    (hini : initial∈S) (hS : ∀ l∈S,TM2.SupportsStmt S (M l)) (a : Fin n → ℕ) :
    Counter.Halts (counterProgram M initial S) (counterInput a) ↔
      (eval (TM2.step M) ⟨some initial,none,K'.elim (trList (List.ofFn a)) [] [] []⟩).Dom := by
  let c : Macro.Cfg (FiniteState n M S) (Reg n) := ⟨some (finStart M S),initValues [] [] a⟩
  have hstep := program_within M initial (statements M S) (statements_self M S hini)
    (statements_sub M S) (statements_goto M S hS) (n:=n)
  have henc : Macro.encode c=⟨(counterProgram M initial S).start,counterInput a⟩ := by
    rw [counterInput_eq]
    rfl
  have hfin := Macro.restrict_eval_dom (program M initial) (Good (statements M S)) (finStart M S) hstep c
  have htrace := reaches_eval (initialize_reaches M initial a).to_reflTransGen
  have hsim := eval_dom M initial ⟨some initial,none,K'.elim (trList (List.ofFn a)) [] [] []⟩ (fun _ : Fin n=>0)
  calc
    Counter.Halts (counterProgram M initial S) (counterInput a) ↔
        (eval (Counter.step (counterProgram M initial S)) (Macro.encode c)).Dom := by
          rw [henc]; exact (Counter.eval_dom_iff_halts _ _).symm
    _ ↔ (eval (Macro.step (finProgram M initial S)) c).Dom := Macro.eval_dom _ _ c
    _ ↔ (eval (Macro.step (program M initial)) (initCfg (.start (Fin.last n)) [] [] a)).Dom := hfin
    _ ↔ (eval (Macro.step (program M initial))
      (codeCfg (M initial) none (K'.elim (trList (List.ofFn a)) [] [] []) (fun _=>0))).Dom := by rw [htrace]
    _ ↔ _ := hsim

lemma exists_code {p : (Fin n → ℕ) → Prop} (hp : REPred p) :
    ∃ c : ToPartrec.Code,∀a,(ToPartrec.Code.eval c (List.ofFn a)).Dom ↔ p a := by
  let f (v : List.Vector ℕ n) : Part ℕ :=
    (Part.assert (p v.get) (fun _=>Part.some ())).map (fun _=>0)
  have hf : Partrec f := (hp.comp Primrec.vector_get'.to_comp).map (Computable.const 0).to₂
  obtain ⟨c,hc⟩:=ToPartrec.Code.exists_code (Nat.Partrec'.of_part hf)
  refine ⟨c,fun a=>?_⟩
  rw [←List.Vector.toList_ofFn a]
  change (ToPartrec.Code.eval c (List.Vector.ofFn a).val).Dom ↔p a
  rw [hc]
  have hg : (List.Vector.ofFn a).get=a := funext (List.Vector.get_ofFn a)
  change (∃ _ : p (List.Vector.ofFn a).get, True) ↔p a
  rw [hg]
  simp

theorem exists_counter {p : (Fin n → ℕ) → Prop} (hp : REPred p) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : Counter.Machine Q (Macro.Reg (Reg n))),
      ∀a, p a ↔ Counter.Halts M (counterInput a) := by
  obtain ⟨c,hc⟩:=exists_code hp
  let initial := trNormal c Cont'.halt
  let S := codeSupp c Cont'.halt
  have hS := tr_supports c Cont'.halt
  refine ⟨Macro.State (FiniteState n tr S),inferInstance,inferInstance,counterProgram tr initial S,fun a=>?_⟩
  rw [counter_halts tr initial S hS.1 hS.2]
  change p a ↔ (eval (TM2.step tr) (init c (List.ofFn a))).Dom
  rw [PartrecToTM2.tr_eval]
  exact (hc a).symm
end SingleFold.TM2Macro

end

end OAI
