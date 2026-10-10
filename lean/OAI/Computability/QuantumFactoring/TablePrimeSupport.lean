import Mathlib
import OAI.Computability.QuantumFactoring.TableOrder
import OAI.Computability.QuantumFactoring.PrimeComponentCircuit
import OAI.Computability.QuantumFactoring.RetrospectiveResidues

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree
namespace PhysicalTree

lemma tableFactors_cover {n N M m : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hM0 : M≠0)
    (_hm : m≠0) (hd : m∣M) : ∀ p : ℕ,p.Prime→p∣m→p∈tableFactors rows := by
  intro p hp hpm
  have hh:=lookupPrimes_correct h hM hM0
  have hpM : p∣(lookupPrimes rows M).prod := by rw [hh.2];exact hpm.trans hd
  obtain ⟨q,hq,hpq⟩:=(Nat.prime_iff.mp hp).dvd_prod_iff.mp hpM
  have he:=((hh.1 q hq).eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one
  have hpq' : p∈lookupPrimes rows M := by simpa only [he] using hq
  exact lookupPrimes_subset_table hM0 hpq'

end PhysicalTree

/-- A distinguished component can be tested by polynomially many pairwise
comparisons, without constructing the least prime factor of an unknown N. -/
def leastDivisorIn (ps : List ℕ) (m p : ℕ) : Prop := ∀ q∈ps,q∣m→p≤q

lemma leastDivisorIn_iff {ps : List ℕ} {m p : ℕ} (hm : 2 ≤ m)
    (hps : ∀ q∈ps,q.Prime) (hcover : ∀ q : ℕ,q.Prime→q∣m→q∈ps)
    (hp : p∈ps) (hpd : p∣m) : leastDivisorIn ps m p ↔ p=m.minFac := by
  have hmin : m.minFac∈ps := hcover _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd m)
  constructor
  · intro h
    exact le_antisymm (h _ hmin (Nat.minFac_dvd m)) (Nat.minFac_le_of_dvd (hps p hp).two_le hpd)
  · rintro rfl q hq hqd
    exact Nat.minFac_le_of_dvd (hps q hq).two_le hqd

/-- Redundant rectangular-table entries and harmless dummy primes are ignored
unless they divide m; duplicates impose exactly the same congruence. -/
noncomputable def tableCanonical (ps : List ℕ) (a m n : ℕ) : Prop := by
  classical
  exact a < m ∧ ∀ p∈ps,p∣m→a%(Nat.gcd m (p^n))=
    if leastDivisorIn ps m p then 1 else Nat.gcd m (p^n)-1

lemma tableCanonical_correct {ps : List ℕ} {M m n : ℕ} (hM : 0 < M) (hm : 2 ≤ m)
    (hb : m ≤ 2^n) (hd : m∣M) (hps : ∀ q∈ps,q.Prime)
    (hcover : ∀ q : ℕ,q.Prime→q∣m→q∈ps) (a : ℕ) :
    tableCanonical ps a m n ↔ dataCanonicalResidue (trueData M) a m := by
  rw [tableCanonical,dataCanonicalResidue,dataRecord_correct hM hd,recordFirst_factorization hm]
  apply and_congr_right
  intro _
  constructor
  · intro h p hp
    obtain ⟨hprime,hpd,_⟩:=Nat.mem_primeFactors.mp hp
    have hmem:=hcover p hprime hpd
    have hh:=h p hmem hpd
    simpa only [prime_component_gcd (by omega) hprime hb,
      leastDivisorIn_iff hm hps hcover hmem hpd] using hh
  · intro h p hp hpd
    have hh:=h p (Nat.mem_primeFactors.mpr ⟨hps p hp,hpd,by omega⟩)
    simpa only [prime_component_gcd (by omega) (hps p hp) hb,
      leastDivisorIn_iff hm hps hcover hp hpd] using hh
end ExactQuantumFactoring


end

end OAI
