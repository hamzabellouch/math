import Mathlib
import OAI.Computability.QuantumFactoring.NodeStateNil

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController
namespace NodeStateCircuit

/-- Failed candidates leave genuine pending factors unchanged and only set the
sticky verifier bit. They cannot introduce an unrelated query into the log. -/
lemma step_failure {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w)
    (xs ys : List (Basis w)) (b : Bool) (hx : xs.length ≤ s)
    (ha : 2 ≤ (bitsValue a).toNat) (hp : ¬(bitsValue a).toNat.Prime)
    (hd : ¬ProperDivisor (bitsValue a).toNat (bitsValue d).toNat) :
    (step s w).eval (Fin.append (pack (a::xs) ys b) d)=pack (a::xs) ys true := by
  have he : (emission s w).eval (Fin.append (pack (a::xs) ys b) d)=(fun _=>false) := by
    rw [emission,eval_comp,nodeInput_pack,NodeCircuit.emitted_pack_cons hw,ite_eq_right hp]
  have hz : (zeroWord (emission s w)).eval (Fin.append (pack (a::xs) ys b) d) 0=true := by
    rw [zeroWord_value,he,zeroBasis_value]
    rfl
  have hf : (NodeCircuit.failed s w).eval (NodeCircuit.pack (a::xs) d) 0=true :=
    (NodeCircuit.failed_pack_cons hw a d xs ha).mpr ⟨hp,hd⟩
  have hb : (nextBad s w).eval (Fin.append (pack (a::xs) ys b) d)=(fun _=>true) := by
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    rw [nextBad,eval_bor,eval_comp,old_append,bad_pack,eval_comp,nodeInput_pack,hf,Bool.or_true]
  rw [step,eval_pair,eval_pair,nextPending,eval_comp,nodeInput_pack,
    NodeCircuit.next_pack_cons hw _ _ _ hx ha,ite_eq_right hp,ite_eq_right hd,nextOutput,wordMux_eval,
    ite_eq_left hz,eval_comp,old_append,output_pack,hb]
  rfl
end NodeStateCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
