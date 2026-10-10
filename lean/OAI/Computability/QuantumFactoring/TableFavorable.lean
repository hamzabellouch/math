import Mathlib
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

lemma table_pairwise_iff {ps : List ℕ} {m : ℕ} (hm : 2 ≤ m)
    (hps : ∀ p∈ps,p.Prime) (hcover : ∀ p : ℕ,p.Prime→p ∣ m→p∈ps) (v : ℕ→ℕ) :
    (∀ p∈ps,p ∣ m→∀ q∈ps,q ∣ m→v p=v q) ↔
      ∀ p∈m.primeFactors,v p=v m.minFac := by
  have hmin:=hcover m.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd m)
  constructor
  · intro h p hp
    have H:=Nat.mem_primeFactors.mp hp
    exact h p (hcover p H.1 H.2.1) H.2.1 _ hmin (Nat.minFac_dvd m)
  · intro h p hp hpd q hq hqd
    have hp':=Nat.mem_primeFactors.mpr ⟨hps p hp,hpd,by omega⟩
    have hq':=Nat.mem_primeFactors.mpr ⟨hps q hq,hqd,by omega⟩
    exact (h p hp').trans (h q hq').symm

/-- Pairwise comparison avoids searching for a least component. The supplied
rectangular table may contain duplicates and harmless primes not dividing m. -/
noncomputable def tableFavorable (ps : List ℕ) (data : FactorData) (a m n : ℕ) : Prop :=
  a < m  ∧  a.Coprime m  ∧   ¬ ∀ p∈ps,p ∣ m→∀ q∈ps,q ∣ m→
    padicValNat 2 (dataOrder data a (Nat.gcd m (p^n)))=
      padicValNat 2 (dataOrder data a (Nat.gcd m (q^n)))

lemma tableFavorable_correct {ps : List ℕ} {P m n : ℕ} (hP : 0 < P) (hm : 2 ≤ m)
    (hb : m ≤ 2^n) (hd : m ∣ P) (hps : ∀ p∈ps,p.Prime)
    (hcover : ∀ p : ℕ,p.Prime→p ∣ m→p∈ps) (a : ℕ) :
    tableFavorable ps (trueData P) a m n ↔ dataResidueGood (trueData P) a m := by
  rw [tableFavorable,dataResidueGood,dataRecord_correct hP hd,recordFirst_factorization hm]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply not_congr
  have he : (∀ p∈ps,p ∣ m→∀ q∈ps,q ∣ m→
      padicValNat 2 (dataOrder (trueData P) a (Nat.gcd m (p^n)))=
        padicValNat 2 (dataOrder (trueData P) a (Nat.gcd m (q^n)))) ↔
      ∀ p∈ps,p ∣ m→∀ q∈ps,q ∣ m→
        padicValNat 2 (dataOrder (trueData P) a (p^m.factorization p))=
          padicValNat 2 (dataOrder (trueData P) a (q^m.factorization q)) := by
    apply forall_congr';intro p
    apply forall_congr';intro hp
    apply forall_congr';intro _
    apply forall_congr';intro q
    apply forall_congr';intro hq
    rw [prime_component_gcd (by omega) (hps p hp) hb,prime_component_gcd (by omega) (hps q hq) hb]
  exact he.trans (table_pairwise_iff hm hps hcover _)
end ExactQuantumFactoring


end

end OAI
