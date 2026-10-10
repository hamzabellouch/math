import Mathlib
import OAI.Computability.QuantumFactoring.QuarterPreparation
import OAI.Computability.QuantumFactoring.TreePhysicalPreparation

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

lemma hadamards_zero_encoded (q : ℕ) :
    (programMatrix (hadamardPrefix q q le_rfl)).mulVec (basisVector (fun _=>false))=
      encodeState id (fairState q) := by
  funext x
  rw [hadamards_zero]
  exact (encodeState_at id Function.injective_id (fairState q) x).symm

namespace Completion
/-- The actual four-register completion, when the ordinary preparation has
retained and injectively encoded its full history. -/
def extendEncoding {α : Type*} {q : ℕ} (e : α→Basis q) (W t d : ℕ) :
    Raw α W t d→Basis (t+(q+(W+coinBits W t d))) :=
  fun r=>Fin.append r.1 (Fin.append (e r.2.1) (Fin.append r.2.2.1 r.2.2.2))

lemma extendEncoding_injective {α : Type*} {q : ℕ} (e : α→Basis q)
    (he : Function.Injective e) (W t d : ℕ) : Function.Injective (extendEncoding e W t d) := by
  rintro ⟨a,b,c,h⟩ ⟨a',b',c',h'⟩ hh
  have H : (a,Fin.append (e b) (Fin.append c h))=
      (a',Fin.append (e b') (Fin.append c' h')) :=
    (appendEquiv t (q+(W+coinBits W t d))).injective hh
  have ha:=congrArg Prod.fst H
  have H' : (e b,Fin.append c h)=(e b',Fin.append c' h') :=
    (appendEquiv q (W+coinBits W t d)).injective (congrArg Prod.snd H)
  have hb:=he (congrArg Prod.fst H')
  have H'' : (c,h)=(c',h') :=
    (appendEquiv W (coinBits W t d)).injective (congrArg Prod.snd H')
  have hc:=congrArg Prod.fst H''
  have hd:=congrArg Prod.snd H''
  cases ha; cases hb; cases hc; cases hd; rfl

lemma program_encoded_state {α : Type*} [Fintype α] {q : ℕ}
    (P : List (Instruction q)) (e : α→Basis q) (ψ : α→ℂ) (z : Basis q)
    (hP : (programMatrix P).mulVec (basisVector z)=encodeState e ψ) (W t d : ℕ) :
    (programMatrix (program P W t d)).mulVec
      (basisVector (layout q W t d ((fun _=>false),z,(fun _=>false),(fun _=>false))))=
      encodeState (extendEncoding e W t d) (fresh ψ W t d) := by
  let D:=coinBits W t d
  have hG := parallelProgram_encoded_state
    (hadamardPrefix W W le_rfl) (hadamardPrefix D D le_rfl)
    (fun _=>false) (fun _=>false) id id (fairState W) (fairState D)
    (hadamards_zero_encoded W) (hadamards_zero_encoded D)
  have hO := parallelProgram_encoded_state P
    (parallelProgram (hadamardPrefix W W le_rfl) (hadamardPrefix D D le_rfl))
    z (Fin.append (fun _ : Fin W=>false) (fun _ : Fin D=>false)) e
    (fun r : Basis W×Basis D=>Fin.append r.1 r.2) ψ
    (independentState (fairState W) (fairState D)) hP hG
  have hT := parallelProgram_encoded_state
    (hadamardPrefix t t le_rfl)
    (parallelProgram P (parallelProgram (hadamardPrefix W W le_rfl) (hadamardPrefix D D le_rfl)))
    (fun _=>false) (Fin.append z (Fin.append (fun _ : Fin W=>false) (fun _ : Fin D=>false)))
    id (fun r : α×(Basis W×Basis D)=>Fin.append (e r.1) (Fin.append r.2.1 r.2.2))
    (fairState t) (independentState ψ (independentState (fairState W) (fairState D)))
    (hadamards_zero_encoded t) hO
  exact hT
end Completion

namespace PhysicalTree
abbrev quarterWidth (n : ℕ) := 1+(paddedWidth n+(n*n+Quarter.D n))
def quarterProgram (n : ℕ) : List (Instruction (quarterWidth n)) :=
  Quarter.program (paddedProgram n) n
def quarterZero (n N : ℕ) : Basis (quarterWidth n) :=
  Completion.layout (paddedWidth n) (n*n) 1 (n^11)
    ((fun _=>false),paddedZero n N,(fun _=>false),(fun _=>false))
def quarterEncoding (n N : ℕ) : Quarter.Raw (PaddedRaw n) n→Basis (quarterWidth n) :=
  Completion.extendEncoding (paddedEncoding n N) (n*n) 1 (n^11)

lemma quarterProgram_state (n N : ℕ) :
    (programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))=
      encodeState (quarterEncoding n N) (Quarter.fresh (paddedState n N) n) :=
  Completion.program_encoded_state _ _ _ _ (paddedProgram_state n N) _ _ _
lemma quarterEncoding_injective (n N : ℕ) : Function.Injective (quarterEncoding n N) :=
  Completion.extendEncoding_injective _ (paddedEncoding_injective n N) _ _ _
lemma quarterProgram_length (n : ℕ) :
    (quarterProgram n).length=(paddedProgram n).length+1+n*n+Quarter.D n :=
  Quarter.program_length _ _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
