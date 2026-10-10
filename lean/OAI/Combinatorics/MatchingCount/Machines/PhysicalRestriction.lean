import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.PhysicalPost

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q : Type} [Inhabited Γ]

def Supported (M : Table Γ Q) (S : Finset Q) : Prop :=
  ∀ q ∈ S, ∀ a b q' act,M q a b=some (q',act) → q'∈S

noncomputable def restrict (M : Table Γ Q) (S : Finset Q) (_h : Supported M S) :
    Table Γ {q // q∈S} := by
  classical
  exact fun q a b=>(M q.val a b).map (fun qa=>
    ((if hm:qa.1∈S then ⟨qa.1,hm⟩ else q),qa.2))

def liftCfg (S : Finset Q) (c : Cfg Γ {q // q∈S}) : Cfg Γ Q :=
  ⟨c.state.map Subtype.val,c.tape⟩

lemma tick_lift (M : Table Γ Q) (S : Finset Q) (h : Supported M S)
    (c : Cfg Γ {q // q∈S}) (b : Bool) :
    tick M (liftCfg S c) b=liftCfg S (tick (restrict M S h) c b) := by
  cases c with
  | mk state T => cases state with
    | none => rfl
    | some q =>
      cases e:M q.val T.head b with
      | none => simp only [tick,liftCfg,Option.map_some,restrict,e,Option.map_none]
      | some qa =>
        rcases qa with ⟨q',act⟩
        have hq' : q'∈S:=h q.val q.property T.head b q' act e
        simp only [tick,liftCfg,Option.map_some,restrict,e,dite_eq_left hq']

lemma execute_lift (M : Table Γ Q) (S : Finset Q) (h : Supported M S)
    (n : ℕ) (c : Cfg Γ {q // q∈S}) (b : Stream) :
    execute M n (liftCfg S c) b=liftCfg S (execute (restrict M S h) n c b) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => rw [execute,tick_lift,ih,execute]

noncomputable def restrictedMachine (M : Table Symbol Q) (S : Finset Q)
    (h : Supported M S) (q₀ : Q) (hq₀ : q₀∈S) : RandomMachine :=
  letI : Inhabited {q //q∈S}:=⟨⟨q₀,hq₀⟩⟩
  machine (restrict M S h)

lemma restrictedMachine_run (M : Table Symbol Q) (S : Finset Q)
    (h : Supported M S) (q₀ : Q) (hq₀ : q₀∈S)
    (input : List Symbol) (n : ℕ) (b : Bits n) :
    letI : Inhabited {q //q∈S}:=⟨⟨q₀,hq₀⟩⟩
    MatchingFPRAS.run (restrictedMachine M S h q₀ hq₀) input b=
      sealCfg (restrict M S h)
        (execute (restrict M S h) n ⟨some default,Tape.mk₁ input⟩ (extend b)) :=
by
  let : Inhabited {q //q∈S}:=⟨⟨q₀,hq₀⟩⟩
  exact run_seal (restrict M S h) input n b

end MatchingFPRAS.PhysicalPost

end OAI
