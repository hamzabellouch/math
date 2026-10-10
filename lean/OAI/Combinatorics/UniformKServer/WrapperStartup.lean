import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperResponse
import OAI.Combinatorics.UniformKServer.WrapperPrefix

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}

 theorem construct_input (c : Turing.ToPartrec.Code) (v : List ℕ) (i : BitTape) :
    constructState (qa:=qa) (LiteralPartrec.input c v) i=
      wordState (.construct (LiteralPartrec.processor c).start) i ((trList v).map FlatTM2.letters) [] [] [] true := by
  have h:=LiteralInput.input_config c v
  have hc:=congrArg (fun s=>s.1) h
  have hs:=congrArg (fun s=>s.2.1) h
  have hy:=congrArg (fun s=>s.2.2) h
  change (LiteralPartrec.input c v).control=(LiteralPartrec.processor c).start at hc
  change (LiteralPartrec.input c v).yielded=false at hy
  apply wordState_ext
  · simp only [constructState,inside,hy,Bool.cond_false,hc,wordState]
  · rfl
  · intro k
    cases k with
    | base k=>
      change (LiteralPartrec.input c v).store (FlatTM2.keys k)=_
      have hh:=congrFun hs (FlatTM2.keys k)
      change (LiteralPartrec.input c v).store (FlatTM2.keys k)=
        (if FlatTM2.keys k=FlatTM2.keys K'.main then (trList v).map FlatTM2.letters else []) at hh
      rw [hh]
      cases k <;> simp [wordState]
    | pay=>rfl
    | buf=>rfl
  · rfl
  · rfl

 theorem construct_output {c : Turing.ToPartrec.Code} {v w : List ℕ}
    {t : ℕ} (hy : (StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)).yielded=true)
    (hs : ∀i,(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)).store i=((halt w).stk (FlatTM2.keys.symm i)).map FlatTM2.letters)
    (i : BitTape) :
    constructState (qa:=qa) (StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)) i=wordState .pad i ((trList w).map FlatTM2.letters) [] [] [] true := by
  apply wordState_ext
  · simp only [constructState,inside,hy,Bool.cond_true,wordState]
  · rfl
  · intro k;cases k with
    | base k=>
      simp only [constructState,inside,hs,Equiv.symm_apply_apply,halt,wordState]
      cases k <;> rfl
    | pay=>rfl
    | buf=>rfl
  · rfl
  · rfl

 theorem literal_first {c : Turing.ToPartrec.Code} {v w : List ℕ}
    (h : w∈Turing.ToPartrec.Code.eval c v) :
    ∃t,(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)).yielded=true ∧
      (∀j<t,(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
        (List.replicate j false)).yielded=false) ∧
      ∀i,(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
        (List.replicate t false)).store i=((halt w).stk (FlatTM2.keys.symm i)).map FlatTM2.letters := by
  obtain ⟨T,hT,hS⟩:=LiteralPartrec.halts h
  have he : ∃t,(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)).yielded=true:=⟨T,hT⟩
  have ht:=Nat.find_spec he
  refine ⟨Nat.find he,ht,?_,?_⟩
  · intro j hj
    have hn:=Nat.find_min he hj
    cases hh:(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate j false)).yielded <;> simp_all
  · rw [←StackCompiler.capped_after _ _ ht (Nat.find_min' he hT)]
    exact hS

 theorem literal_prefix {c : Turing.ToPartrec.Code} {v w : List ℕ}
    (h : w∈Turing.ToPartrec.Code.eval c v)
    (A : StackCompiler.Processor qa (Fintype.card K') g) :
    ∃t,Nonempty (Prefix (processor (LiteralPartrec.processor c) A)
      (wordState (.construct (LiteralPartrec.processor c).start) BitTape.blank ((trList v).map FlatTM2.letters) [] [] [] true)
      (wordState .pad BitTape.blank ((trList w).map FlatTM2.letters) [] [] [] true) t) := by
  obtain ⟨t,ht,hp,hs⟩:=literal_first h
  have hh:=constructor_prefix (LiteralPartrec.processor c) A (StackPrimitive.literal_deterministic c)
    (LiteralPartrec.input c v) t hp
  rw [construct_input,construct_output ht hs] at hh
  exact ⟨t,⟨hh⟩⟩

 theorem startup_exists (mult a : ℕ) (v : ConstructorSearch.Cert)
    (h : v∈ConstructorSearch.search mult (ConstructorProgram.read a)) :
    ∃d,2^v.2.2≤d ∧ Nonempty (Prefix (uniform mult)
      (wordState (.construct (literalC mult).start) BitTape.blank ((trList [a]).map FlatTM2.letters) [] [] [] true)
      (ready (RuntimeCertificate.B (ConstructorProgram.read a).2.1 v.1)
        (Encodable.encode (RawProgram.initial (ConstructorProgram.read a).1 (ConstructorProgram.read a).2.1 v.1))
        BitTape.blank [] true) d) := by
  obtain ⟨t,⟨hp⟩⟩:=literal_prefix (ConstructorProgram.code_correct h) literalA
  let b:=RuntimeCertificate.B (ConstructorProgram.read a).2.1 v.1
  let u:=Encodable.encode (RawProgram.initial (ConstructorProgram.read a).1 (ConstructorProgram.read a).2.1 v.1)
  change Prefix (uniform mult) _
    (wordState .pad BitTape.blank ((trList [2^(2^v.2.2),2^b,u]).map FlatTM2.letters) [] [] [] true) t at hp
  rw [encodedList (2^(2^v.2.2))] at hp
  have hq:=padding_prefix (literalC mult) literalA (2^(2^v.2.2)).bits
    ((trList [2^b,u]).map FlatTM2.letters)
  have hh:=hp.append hq
  refine ⟨t+((2^(2^v.2.2):ℕ).bits.length+1),?_,⟨hh⟩⟩
  rw [pow_bits,List.length_append,List.length_replicate,List.length_singleton]
  omega

end UniformKServer.UniformWrapper

end

end OAI
