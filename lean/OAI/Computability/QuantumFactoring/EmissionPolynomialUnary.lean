import Mathlib
import OAI.Computability.QuantumFactoring.PolyAt
import OAI.Computability.QuantumFactoring.BitStackBoundedUnary
import OAI.Computability.QuantumFactoring.EmissionLists

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool}
lemma unaryPow {f : α→ℕ} (hf : Emits ea unaryCode f) (k : ℕ) : Emits ea unaryCode (fun x=>(f x)^k):=by
  induction k with
  | zero=>simpa only [pow_zero] using (const ea unaryCode 1)
  | succ k ih=>simpa only [pow_succ] using ih.unaryMul hf
lemma unaryPolynomial (p : Polynomial ℕ) {f : α→ℕ} (hf : Emits ea unaryCode f) :
    Emits ea unaryCode (fun x=>p.eval (f x)):=by
  induction p using Polynomial.induction_on' with
  | add p q hp hq=>simpa only [Polynomial.eval_add] using hp.unaryAdd hq
  | monomial k c=>simpa only [Polynomial.eval_monomial] using (const ea unaryCode c).unaryMul (hf.unaryPow k)
lemma boundedUnary {f B : α→ℕ} (hf : Emits ea Nat.bits f) (hB : Emits ea unaryCode B)
    (h : ∀x,f x≤B x) : Emits ea unaryCode f:=by
  obtain ⟨p⟩:=hf;obtain ⟨q⟩:=hB
  exact ⟨Procedure.boundedUnary p q h⟩
lemma ofPolyAt {f len : α→ℕ} (hf : Emits ea Nat.bits f) (hl : Emits ea unaryCode len) (hb : PolyAt len f) :
    Emits ea unaryCode f:=by
  obtain ⟨p,hp⟩:=hb
  exact hf.boundedUnary (unaryPolynomial p hl) hp
lemma ofPolyBound {f : ℕ→ℕ} (hf : Emits unaryCode Nat.bits f) (hb : PolyBound f) :
    Emits unaryCode unaryCode f:=hf.ofPolyAt (id _) hb
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
