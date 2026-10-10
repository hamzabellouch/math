import Mathlib
import OAI.Computability.QuantumFactoring.AuxiliaryData

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

noncomputable def primeRecord : List ℕ→FactorRecord
  | [] => 0
  | p::ps => Finsupp.single p 1+primeRecord ps

lemma primeRecord_eq_factorization (ps : List ℕ) (hp : ∀ p∈ps,p.Prime) :
    primeRecord ps=ps.prod.factorization := by
  induction ps with
  | nil => simp [primeRecord]
  | cons p ps ih =>
    have hprime := hp p (by simp)
    have ht : ∀ q∈ps,q.Prime := fun q hq => hp q (by simp [hq])
    have hprod : ps.prod≠0 := by
      apply List.prod_ne_zero
      intro hzero
      exact (ht 0 hzero).ne_zero rfl
    rw [primeRecord,List.prod_cons,Nat.factorization_mul hprime.ne_zero hprod,
      hprime.factorization,ih ht]

end ExactQuantumFactoring


end

end OAI
