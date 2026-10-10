import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalTreeLaunch
import OAI.Computability.QuantumFactoring.NodeVerifiedCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)
lemma first_verified (x : Basis c) (t : ℕ) (h : Trace n (t+1))
    (hp : M.verified x (t+1) h) :
    PhysicalTree.NodeVerified (M.query.eval x) (firstRaw t h) := by
  induction t with
  | zero=>exact hp.2
  | succ t ih=>exact ih h.1 hp.1
end NodeMachine
namespace PhysicalTree
lemma nodeWords_layout (n : ℕ) (z : Basis (NodeKernel.width n)) :
    SortedWords.layout n n (nodeWords n z)=(nodeResult n).eval z := by
  simp only [nodeWords,SortedWords.layout_ofFn,resultFields,eval_comp,tensorSelect_inverse]
  exact (tensorLayout n n).apply_symm_apply _

/-- The literal data-verifier flag implies a correct root readout on arbitrary
raw histories, not just on histories assumed successful in the analysis. -/
theorem verified_root {n N : ℕ} (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (h : NodeMachine.Trace n (t+1))
    (hp : (machine n).verified (initialQueue n N) (t+1) h) :
    ∃ zs : List (Basis n), zs.length=n ∧ CorrectEncoding N n (SortedWords.numbers zs) ∧
      (rootResult n t).eval ((machine n).encoded (initialQueue n N) (t+1) h)=
        SortedWords.layout n n zs := by
  have hp0:=(machine n).first_verified (initialQueue n N) t h hp
  change NodeVerified ((query n).eval (initialQueue n N)) (NodeMachine.firstRaw t h) at hp0
  rw [query_initial] at hp0
  have hv : (bitsValue (natBasis n N)).toNat=N := by rw [natBasis_value,Nat.mod_eq_of_lt hb]
  rcases hp0 with hz | hc
  · rw [hv] at hz
    omega
  · refine ⟨nodeWords n (NodeKernel.encoding (natBasis n N) (NodeMachine.firstRaw t h)),
      nodeWords_length _ _,?_,?_⟩
    · simpa only [hv] using hc
    · rw [rootResult,eval_comp,NodeMachine.firstNodeNet_encoded,nodeWords_layout]
      change (nodeResult n).eval (NodeKernel.encoding ((query n).eval (initialQueue n N)) _) = _
      rw [query_initial]

/-- Exact equivalence of the physical data-verifier bit with the explicit
retrospective data predicate, and its unconditional root-output soundness. -/
theorem verifier_readout {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (h : NodeMachine.Trace n (t+1))
    (hp : ((machine n).verifiedNet (t+1)).eval
      ((machine n).encoded (initialQueue n N) (t+1) h) 0=true) :
    ∃ zs : List (Basis n), zs.length=n ∧ CorrectEncoding N n (SortedWords.numbers zs) ∧
      (rootResult n t).eval ((machine n).encoded (initialQueue n N) (t+1) h)=
        SortedWords.layout n n zs :=
  verified_root hN hb t h (((machine n).verifiedNet_encoded hn _ _ _).mp hp)
end PhysicalTree
end ExactQuantumFactoring


end

end OAI
