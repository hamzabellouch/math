import Mathlib
import OAI.Computability.QuantumFactoring.FixedSplit
import OAI.Computability.QuantumFactoring.HardCofactor

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials OrderTrial
namespace UniversalSplit

/-- The unchanging request register dimensions depend only on the original n. -/
abbrev Raw := FixedSplit.Raw

def Hard (m : ℕ) : Prop := 2 ≤ m ∧ ¬m.Prime ∧ Odd m ∧ ¬Primality.PerfectPower m

/-- Source's distinguished component: the least prime divisor, not an arbitrary
component for which the compiler would need extra advice. -/
def firstComponent {m : ℕ} (hm : 2 ≤ m) : Component m :=
  ⟨m.minFac,Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd m,by omega⟩⟩

lemma secondComponent {m : ℕ} (hm : Hard m) :
    ∃ p₁ : Component m,p₁≠firstComponent hm.1 := by
  classical
  obtain ⟨a,b,hne⟩ := exists_distinct_components hm.1 hm.2.1 hm.2.2.2
  by_cases ha : a=firstComponent hm.1
  · exact ⟨b,by simpa only [←ha] using hne⟩
  · exact ⟨a,ha⟩

noncomputable def dummyList {n : ℕ} : PhysicalListSlots.Result n→Prop :=
  Completion.passed (fun _=>True) (natBasis _ 0) 1 (Completion.target n)
noncomputable def dummyOrder {n : ℕ} : OrderSlots.Result n→Prop :=
  Completion.passed (fun _=>True) (natBasis _ 0) 1 (Completion.target n)
noncomputable def dummy {n : ℕ} (r : Raw n) : Prop := dummyList r.1 ∧ ∀ i,dummyOrder (r.2 i)

lemma dummy_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) :
    outcomeMass dummy (FixedSplit.fresh m)=(Completion.target n:ℝ)^(n^5+1) := by
  change outcomeMass (fun r : Raw n => dummyList r.1 ∧ (fun (_ : PhysicalListSlots.Result n)
    (rr : Fin (n^5)→OrderSlots.Result n)=>∀ i,dummyOrder (rr i)) r.1 r.2)
      (RecordedHistory.appendState _ _) = _
  have ho : ∀ l : PhysicalListSlots.Result n, outcomeMass
      (fun rr : Fin (n^5)→OrderSlots.Result n => ∀ i,dummyOrder (rr i))
      (productState (fun i=>OrderSlots.fresh n (FixedSplit.bases l i) m))=
        (Completion.target n:ℝ)^(n^5) := by
    intro l
    rw [productState_all_mass]
    have he : ∀ i : Fin (n^5),outcomeMass dummyOrder
        (OrderSlots.fresh n (FixedSplit.bases l i) m)=(Completion.target n:ℝ) := by
      intro i
      exact Completion.dummy_passed_mass _ n _ hn
        (tensor_normalized _ _ (raw_normalized _ _ _ _)) (natBasis _ 0)
    simp only [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [RecordedHistory.append_constant_mass (PhysicalListSlots.fresh m)
    (fun l=>productState (fun i=>OrderSlots.fresh n (FixedSplit.bases l i) m))
    dummyList (fun _ rr=>∀ i,dummyOrder (rr i)) ((Completion.target n:ℝ)^(n^5)) (fun l _=>ho l)]
  have hl := Completion.dummy_passed_mass (PhysicalListSlots.ordinaryState m) n (n*n^5)
    hn (PhysicalListSlots.ordinary_normalized m) (natBasis _ 0)
  change outcomeMass dummyList (PhysicalListSlots.fresh m)=(Completion.target n:ℝ) at hl
  rw [hl]
  exact (mul_comm _ _).trans (pow_succ (Completion.target n:ℝ) (n^5)).symm

noncomputable def passed {n : ℕ} (m : Basis n) : Raw n→Prop := by
  classical
  exact if h : Hard (bitsValue m).toNat then
    FixedSplit.passed m (by have := h.1; omega) (firstComponent h.1) else dummy

lemma passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) :
    outcomeMass (passed m) (FixedSplit.fresh m)=(Completion.target n:ℝ)^(n^5+1) := by
  classical
  unfold passed
  split_ifs with h
  · obtain ⟨p₁,hne⟩ := secondComponent h
    exact FixedSplit.passed_mass hn m h.1 h.2.2.1 (firstComponent h.1) p₁ hne
  · exact dummy_mass hn m

lemma passed_divisor {n : ℕ} (hn : 128 ≤ n) (m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hc : ¬(bitsValue m).toNat.Prime)
    (r : Raw n) (hr : passed m r) :
    FactorController.ProperDivisor (bitsValue m).toNat (FixedSplit.divisor m r) := by
  classical
  have hh := hr
  unfold passed at hh
  split_ifs at hh with h
  · obtain ⟨p₁,hne⟩ := secondComponent h
    exact FixedSplit.passed_divisor hn m hm hc h.2.2.1 (firstComponent h.1) p₁ hne r hh
  · apply suppliedDivisor_good hm (bitsValue m).isLt hc
    intro ho hpow
    exact False.elim (h ⟨hm,hc,ho,hpow⟩)

/-- Every quantum preparation below is the same physical fixed-width program
(on the runtime input word). Hard/easy tests affect the deferred predicate only. -/
noncomputable def fresh (n m : ℕ) : Raw n→ℂ := FixedSplit.fresh (natBasis n m)
noncomputable def good (n m : ℕ) : Raw n→Prop := passed (natBasis n m)
noncomputable def decode (n m : ℕ) (r : Raw n) : ℕ := FixedSplit.divisor (natBasis n m) r

lemma fresh_normalized (n m : ℕ) : ∑ r,Complex.normSq (fresh n m r)=1 :=
  FixedSplit.fresh_normalized _
lemma good_mass {n : ℕ} (hn : 128 ≤ n) (m : ℕ) :
    outcomeMass (good n m) (fresh n m)=(Completion.target n:ℝ)^(n^5+1) := passed_mass hn _

lemma good_divisor {n m : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hb : m<2^n) (hc : ¬m.Prime)
    (r : Raw n) (hr : good n m r) : FactorController.ProperDivisor m (decode n m r) := by
  have he : (bitsValue (natBasis n m)).toNat=m := by simpa only [natBasis_value] using Nat.mod_eq_of_lt hb
  have hh := passed_divisor hn (natBasis n m) (by simpa only [he] using hm)
    (by simpa only [he] using hc) r hr
  simpa only [he,decode] using hh

end UniversalSplit
end ExactQuantumFactoring


end

end OAI
