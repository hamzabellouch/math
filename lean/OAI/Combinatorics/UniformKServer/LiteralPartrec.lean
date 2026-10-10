import Mathlib
import OAI.Combinatorics.UniformKServer.FlatTermination

namespace OAI

noncomputable section

namespace UniformKServer.LiteralPartrec
open Turing Turing.ToPartrec Turing.PartrecToTM2 StackCompiler
open scoped Classical

instance : Fintype K' := ⟨{.main,.rev,.aux,.stack},by intro i;cases i <;> simp⟩

/-- A fixed Partrec program has one fixed finite-control literal processor.
Its parameter is supplied on a stack, not hidden in the transition table. -/
theorem code_exists {α β : Type} [Primcodable α] [Primcodable β]
    (f : α→.β) (hf : Partrec f) :
    ∃c : Code,∀a b,b ∈ f a → ([Encodable.encode b] : List ℕ) ∈ Code.eval c [Encodable.encode a] := by
  let g : ℕ→.ℕ := fun n=>Part.bind (Encodable.decode₂ α n) (fun a=>(f a).map Encodable.encode)
  have hg : Partrec g := Partrec.nat_iff.mpr (Partrec.bind_decode₂_iff.mp hf)
  obtain ⟨c,hc⟩:=ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hg)
  refine ⟨c,?_⟩
  intro a b hb
  have hh:=hc (⟨[Encodable.encode a],by simp⟩ : List.Vector ℕ 1)
  rw [hh]
  change [Encodable.encode b]∈Part.map (fun x=>[x]) (g (Encodable.encode a))
  apply (Part.mem_map_iff _).mpr
  refine ⟨Encodable.encode b,?_,rfl⟩
  dsimp only [g]
  rw [Encodable.encodek₂]
  simp only [Part.coe_some,Part.bind_some]
  exact (Part.mem_map_iff _).mpr ⟨b,hb,rfl⟩

def supp (c : Code) := codeSupp c Cont'.halt

def processor (c : Code) : Processor
    (Fintype.card (FlatTM2.Local tr (supp c))) (Fintype.card K') (Fintype.card Γ') :=
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  FlatTM2.processor tr (supp c) (tr_supports c Cont'.halt) none

def input (c : Code) (v : List ℕ) : State
    (Fintype.card (FlatTM2.Local tr (supp c))) (Fintype.card K') (Fintype.card Γ') :=
  FlatTM2.encode tr (supp c) (FlatTM2.fromCfg tr (PartrecToTM2.init c v))
    (FlatTM2.fromCfg_supported tr (supp c) (PartrecToTM2.init c v)
      (by simp only [PartrecToTM2.init];exact Finset.some_mem_insertNone.mpr (tr_supports c Cont'.halt).1))

theorem halts {c : Code} {v w : List ℕ} (hw : w∈Code.eval c v) :
    ∃t : ℕ,(run (processor c) (input c v) (List.replicate t false)).yielded=true ∧
      ∀i,(run (processor c) (input c v) (List.replicate t false)).store i=
        ((PartrecToTM2.halt w).stk (FlatTM2.keys.symm i)).map FlatTM2.letters := by
  let : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have hh : PartrecToTM2.halt w∈StateTransition.eval (TM2.step tr) (PartrecToTM2.init c v) := by
    rw [PartrecToTM2.tr_eval]
    exact (Part.mem_map_iff _).mpr ⟨w,hw,rfl⟩
  exact FlatTM2.processor_halts tr (supp c) (tr_supports c Cont'.halt) none
    (PartrecToTM2.init c v) (PartrecToTM2.halt w)
    (by simp only [PartrecToTM2.init];exact Finset.some_mem_insertNone.mpr (tr_supports c Cont'.halt).1)
    (StateTransition.mem_eval.mp hh).1 rfl

end UniformKServer.LiteralPartrec

end

end OAI
