import Mathlib
import OAI.Computability.MinUncut.Graphs.UnboundedGraphBase

namespace OAI

section
noncomputable section
namespace MinUncut.Costed.Arena
open _root_.Turing _root_.OAI.Turing Turing.ToPartrec _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Polynomial
open MinUncutGames.Foundations.Complexity MinUncutGames.BinaryEncoding

def initializedGraphMachine (c : Code) : FinTM2 :=
  MachineSequential.machine (codeMachine c) unboundedGraphMachine id .cons
lemma initializedGraphMachine_finite (c : Code) (k : (initializedGraphMachine c).K) :
    Finite ((initializedGraphMachine c).Γ k) :=
  sequential_finiteAlphabet _ _ _ _ (codeMachine_finiteAlphabet _) unboundedGraphMachine_finiteAlphabet k

lemma magnitude_words (xs : List ℕ) : magnitude xs=(encodeWords xs).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih=> simp only [magnitude_cons,encodeWords,List.length_append,encodeWord_length,ih]

lemma exists_graph_initializer {f : ℕ → List ℕ → List ℕ} (P : ∀K,PolyProgram (f K))
    (he : Computable (fun K=>(P K).code)) :
    ∃c : Code,∀K,∃p : Polynomial ℕ,∀xs n table k junk,
      f K xs=n::((table : List Bool).map Bool.toNat++2::k::junk) →
      Nonempty (TM2OutputsInTime (initializedGraphMachine c)
        (trList (K::(encodeWords xs).map FrameDecode.symbol))
        (some (nameBits n++table++nameBits k)) (p.eval (encodeWords xs).length)) := by
  obtain ⟨c,hc⟩:=Init.exists_initializer he
  refine ⟨c,fun K=>?_⟩
  obtain ⟨p,hp⟩:=hc K
  let q:Polynomial ℕ:=p.comp (C (K+1)+C 3*X)
  let r:Polynomial ℕ:=q+1+C 2*(q+1)+unboundedGraphTime.comp ((P K).bound+1+q)
  refine ⟨r,fun xs n table k junk ho=>?_⟩
  let v:=(encodeWords xs).map FrameDecode.symbol
  let b:=Init.base (P K).code xs K v
  let w:=(initialState (P K).code xs b).encode
  have hs:magnitude (K::v)≤(C (K+1)+C 3*X : Polynomial ℕ).eval (encodeWords xs).length:=by
    have hh:=FrameDecode.magnitude_symbols (encodeWords xs)
    simp only [magnitude_cons,eval_add,eval_C,eval_mul,eval_X]
    dsimp only [v]
    omega
  have hpbound:=evalNat_mono p hs
  have hir: Runs c (K::v) w (q.eval (encodeWords xs).length):=
    (hp xs).1.mono (by simpa only [q,eval_comp] using hpbound)
  have his: magnitude w≤q.eval (encodeWords xs).length:=
    (hp xs).2.trans (by simpa only [q,eval_comp] using hpbound)
  have hg:Runs (P K).code xs (n::(table.map Bool.toNat++2::k::junk))
      ((P K).bound.eval (encodeWords xs).length):=by
    have hh:=(P K).run xs
    rw [ho,magnitude_words] at hh
    exact hh
  have hl:(n::(table.map Bool.toNat++2::k::junk)).length≤(P K).bound.eval (encodeWords xs).length:=by
    have hh:=(magnitude_length (f K xs)).trans ((P K).size xs)
    simpa only [ho,magnitude_words] using hh
  let h2:=unboundedGraphMachine_outputs_base b hg hl
  obtain ⟨t,ht,hr⟩:=hir
  let h1:=hr.finiteMachine
  let h2':TM2OutputsInTime unboundedGraphMachine ((trList w).map id)
      (some (nameBits n++table++nameBits k))
      (unboundedGraphTime.eval (magnitude ((P K).bound.eval (encodeWords xs).length::w))) := by
    have input_eq : @List.map (unboundedGraphMachine.Γ unboundedGraphMachine.k₀)
        (unboundedGraphMachine.Γ unboundedGraphMachine.k₀) id (trList w) = trList w :=
      List.map_id _
    simpa only [input_eq] using h2
  have hh:=MachineSequential.execute (codeMachine c) unboundedGraphMachine id Γ'.cons
    _ _ _ _ _ h1 h2'
  have hwb: (trList w).length≤q.eval (encodeWords xs).length:= (bitsize_le_magnitude w).trans his
  have hm:magnitude ((P K).bound.eval (encodeWords xs).length::w)≤
      (((P K).bound+1+q).eval (encodeWords xs).length):=by
    simp only [magnitude_cons,eval_add,eval_one]
    omega
  have hb:=evalNat_mono unboundedGraphTime hm
  simp only [eval_add,eval_one] at hb
  exact ⟨⟨hh.toEvalsTo,hh.steps_le_m.trans (by
    simp only [r,eval_add,eval_one,eval_mul,eval_C,eval_comp]
    change t+1+2*((trList w).length+1)+_≤_
    omega)⟩⟩
end MinUncut.Costed.Arena

end
end

end OAI
