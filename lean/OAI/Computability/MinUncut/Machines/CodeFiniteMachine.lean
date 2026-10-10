import Mathlib
import OAI.Computability.MinUncut.Machines.MachineSubstitution
import OAI.Computability.MinUncut.Estimates.TM2Costed

namespace OAI

section

namespace MinUncut.Costed
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Turing.ToPartrec
noncomputable section

local instance : Fintype K' := ⟨{.main,.rev,.aux,.stack}, by intro k; cases k <;> simp⟩

def codeMachine (c : Code) : FinTM2 where
  K := K'
  k₀ := .main
  k₁ := .main
  Γ _ := Γ'
  Λ := codeSupp c .halt
  main := ⟨trNormal c .halt,codeSupp_self c .halt (trStmts₁_self _)⟩
  σ := Option Γ'
  initialState := none
  m := FiniteControl.program (codeSupp c .halt) tr
    (fun _ h => codeSupp_supports (Finset.Subset.refl _) _ h)

lemma codeMachine_finiteAlphabet (c : Code) (k : (codeMachine c).K) :
    Finite ((codeMachine c).Γ k) := inferInstanceAs (Finite Γ')

lemma codeMachine_init (c : Code) (v : List ℕ) :
    FiniteControl.project (codeSupp c .halt) (initList (codeMachine c) (trList v))=
      ⟨some (trNormal c .halt),none,K'.elim (trList v) [] [] []⟩ := by
  change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k <;> rfl

lemma codeMachine_halt (c : Code) (v : List ℕ) :
    FiniteControl.project (codeSupp c .halt) (haltList (codeMachine c) (trList v))=
      ⟨none,none,K'.elim (trList v) [] [] []⟩ := by
  change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k <;> rfl

def CodeRun.finiteMachine {c v w t} (h : CodeRun c v w t) :
    TM2OutputsInTime (codeMachine c) (trList v) (some (trList w)) (t+1) := by
  apply Classical.choice
  obtain ⟨s,ht⟩ := h.compiled .halt none []
  have he : Within (TM2.step tr) (t+1)
      ⟨some (trNormal c .halt),none,K'.elim (trList v) [] [] []⟩
      ⟨none,none,K'.elim (trList w) [] [] []⟩ :=
    ht.trans (within_one rfl)
  obtain ⟨n,hn,hsteps⟩ := he
  have hi := FiniteControl.projected_iterate (codeMachine c).step (TM2.step tr)
    (FiniteControl.project (codeSupp c .halt))
    (FiniteControl.project_step _ _ (fun _ h => codeSupp_supports (Finset.Subset.refl _) _ h)) n (some (initList (codeMachine c) (trList v)))
  have hs : Steps (codeMachine c).step n
      (initList (codeMachine c) (trList v)) (haltList (codeMachine c) (trList w)) := by
    apply Option.map_injective (FiniteControl.project_injective (codeSupp c .halt))
    dsimp only [Steps] at hsteps ⊢
    exact hi.trans ((congrArg
      (fun cfg : Option (TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ')) =>
        (fun x => x.bind (TM2.step tr))^[n] cfg)
      (congrArg some (codeMachine_init c v))).trans
      (hsteps.trans (congrArg some (codeMachine_halt c w)).symm))
  exact ⟨steps_timed hs hn⟩

end
end MinUncut.Costed

end
section
namespace MinUncut.Costed
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Turing.ToPartrec
open MinUncutGames.Foundations.Complexity
noncomputable section
namespace BooleanAdapter

def encodedWord (b : Bool) : List Γ' := if b then [.bit1,.cons] else [.cons]
def encodeMachine : FinTM2 := WordTransducer.machine () (fun (_ : Unit) (_ : Bool) => ())
  (fun _ b => encodedWord b)

lemma encode_output (v : List Bool) :
    WordTransducer.output (fun (_ : Unit) (_ : Bool) => ()) (fun _ b => encodedWord b) () v=
      trList (v.map Bool.toNat) := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    simp only [List.map_cons,trList,WordTransducer.output]
    rw [ih]
    cases b <;> rfl

def next (q : Bool) : Γ' → Bool
  | .bit1 => true
  | .cons | .consₗ => false
  | .bit0 => q

def emit (q : Bool) : Γ' → List Bool
  | .cons => [q]
  | _ => []

def decodeMachine : FinTM2 := WordTransducer.machine false next emit

lemma decode_output (v : List Bool) :
    WordTransducer.output next emit false (trList (v.map Bool.toNat))=v := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    cases b <;> simp [WordTransducer.output,next,emit,trList,trNat,trNum,trPosNum,ih]

lemma trList_bool_length (v : List Bool) :
    (trList (v.map Bool.toNat)).length≤2*v.length := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    cases b <;> simp [trList,trNat,trNum,trPosNum] <;> omega

def encode_run (v : List Bool) :
    TM2OutputsInTime encodeMachine v (some (trList (v.map Bool.toNat)))
      (2*v.length+(trList (v.map Bool.toNat)).length+2) := by
  have h := WordTransducer.outputsInTime () (fun (_ : Unit) (_ : Bool) => ()) (fun _ b => encodedWord b) v
  erw [encode_output] at h
  exact h

def decode_run (v : List Bool) :
    TM2OutputsInTime decodeMachine (trList (v.map Bool.toNat)) (some v)
      (2*(trList (v.map Bool.toNat)).length+v.length+2) := by
  have h := WordTransducer.outputsInTime false next emit (trList (v.map Bool.toNat))
  erw [decode_output] at h
  exact h

end BooleanAdapter
open BooleanAdapter

def booleanCodeMachine (c : Code) : FinTM2 :=
  MachineSequential.machine
    (MachineSequential.machine encodeMachine (codeMachine c) id .cons)
    decodeMachine id .cons

lemma sequential_finiteAlphabet (a b : FinTM2) (r : a.Γ a.k₁→b.Γ b.k₀)
    (fallback : b.Γ b.k₀) (ha : ∀k,Finite (a.Γ k)) (hb : ∀k,Finite (b.Γ k))
    (k : (MachineSequential.machine a b r fallback).K) :
    Finite ((MachineSequential.machine a b r fallback).Γ k) := by
  rcases k with k | k
  · exact ha k
  · rcases k with k | k
    · exact hb k
    · exact hb b.k₀

lemma booleanCodeMachine_finiteAlphabet (c : Code) (k : (booleanCodeMachine c).K) :
    Finite ((booleanCodeMachine c).Γ k) :=
  sequential_finiteAlphabet _ _ _ _
    (sequential_finiteAlphabet _ _ _ _
      (WordTransducer.finiteAlphabet _ _ _) (codeMachine_finiteAlphabet c))
    (WordTransducer.finiteAlphabet _ _ _) k

def CodeRun.booleanMachine {c : Code} {v w : List Bool} {t : ℕ}
    (h : CodeRun c (v.map Bool.toNat) (w.map Bool.toNat) t) :
    TM2OutputsInTime (booleanCodeMachine c) v (some w) (t+8*v.length+9*w.length+9) := by
  have h₁ := MachineSequential.execute encodeMachine (codeMachine c) id Γ'.cons v _ _ _ _ (encode_run v) (by erw [List.map_id]; exact h.finiteMachine)
  have h₂ := MachineSequential.execute (MachineSequential.machine encodeMachine (codeMachine c) id .cons)
    decodeMachine id Γ'.cons v _ _ _ _ h₁ (by erw [List.map_id]; exact decode_run w)
  have hv := trList_bool_length v
  have hw := trList_bool_length w
  have bound : h₂.steps ≤
      (2 * v.length + (trList (v.map Bool.toNat)).length + 2) +
      2 * ((trList (v.map Bool.toNat)).length + 1) + (t + 1) +
      2 * ((trList (w.map Bool.toNat)).length + 1) +
      (2 * (trList (w.map Bool.toNat)).length + w.length + 2) := h₂.steps_le_m
  refine ⟨h₂.toEvalsTo, le_trans bound ?_⟩
  omega

end
end MinUncut.Costed

end

end OAI
