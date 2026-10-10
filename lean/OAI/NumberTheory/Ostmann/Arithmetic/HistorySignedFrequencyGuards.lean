import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairRepresentatives
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsAncestorsPair
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReductionLocal

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedNumerators
open Construction HistoryOccurrenceVariables HistorySignedDecode HistoryPairPattern HistoryPairRows
open HistoryPairRepresentatives HistorySupportReduction HistorySupportDescent MvPolynomial

def GuardedOwnDivisibility {l : ℕ} (h : History l) (Xp Xm : ℤ) : Prop :=
  ∀ i, AncestorIntegralGuard h Xp Xm i →
    ((internalSlot h i).value : ℤ) ∣ actual h Xp Xm i

variable {l : ℕ} {a : State} {p : ℕ} {u hp hm : List SmallSlot}
  {left right : History l}

theorem guardedOwnDivisibility_left (Xp Xm : ℤ)
    (ho : GuardedOwnDivisibility (.node a p u hp hm left right) Xp Xm)
    (hden : a.frequency * ((u.map SmallSlot.value).prod : ℤ) ≠ 0)
    (hd : a.frequency * ((u.map SmallSlot.value).prod : ℤ) ∣
      reversalNumerator left.root.frequency right.root.frequency
        (Xp * ((hp.map SmallSlot.value).prod : ℤ)) (Xm * ((hm.map SmallSlot.value).prod : ℤ))) :
    GuardedOwnDivisibility left
      (signedPivot ⟨a.frequency, Xp, Xm, a.small⟩ left.root.frequency right.root.frequency u hp hm) Xp := by
  intro i hi
  simpa only [internalSlot, Sum.elim_inr, Sum.elim_inl, actual_node] using
    ho (Sum.inr (Sum.inl i)) ⟨hden, hd, hi⟩

theorem guardedOwnDivisibility_right (Xp Xm : ℤ)
    (ho : GuardedOwnDivisibility (.node a p u hp hm left right) Xp Xm)
    (hden : a.frequency * ((u.map SmallSlot.value).prod : ℤ) ≠ 0)
    (hd : a.frequency * ((u.map SmallSlot.value).prod : ℤ) ∣
      reversalNumerator left.root.frequency right.root.frequency
        (Xp * ((hp.map SmallSlot.value).prod : ℤ)) (Xm * ((hm.map SmallSlot.value).prod : ℤ))) :
    GuardedOwnDivisibility right
      (signedPivot ⟨a.frequency, Xp, Xm, a.small⟩ left.root.frequency right.root.frequency u hp hm) Xm := by
  intro i hi
  simpa only [internalSlot, Sum.elim_inr, actual_node] using
    ho (Sum.inr (Sum.inr i)) ⟨hden, hd, hi⟩

theorem guardedOwnDivisibility_root (Xp Xm : ℤ)
    (ho : GuardedOwnDivisibility (.node a p u hp hm left right) Xp Xm) :
    ∀ b ∈ u, (b.value : ℤ) ∣
      reversalNumerator left.root.frequency right.root.frequency
        (Xp * ((hp.map SmallSlot.value).prod : ℤ)) (Xm * ((hm.map SmallSlot.value).prod : ℤ)) := by
  intro b hb
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hb
  simpa only [internalSlot, Sum.elim_inl, actual_node, hi] using ho (Sum.inl i) trivial

theorem node_integral_of_frequency_and_own {V : ℕ → ℕ} {outside : List ℕ}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hlarge : ∀ b ∈ u, V (l+1) < b.value) (Xp Xm : ℤ)
    (hf : a.frequency ∣ reversalNumerator left.root.frequency right.root.frequency
      (Xp * ((hp.map SmallSlot.value).prod : ℤ)) (Xm * ((hm.map SmallSlot.value).prod : ℤ)))
    (ho : ∀ b ∈ u, (b.value : ℤ) ∣
      reversalNumerator left.root.frequency right.root.frequency
        (Xp * ((hp.map SmallSlot.value).prod : ℤ)) (Xm * ((hm.map SmallSlot.value).prod : ℤ))) :
    a.frequency * ((u.map SmallSlot.value).prod : ℤ) ≠ 0 ∧
      a.frequency * ((u.map SmallSlot.value).prod : ℤ) ∣
        reversalNumerator left.root.frequency right.root.frequency
          (Xp * ((hp.map SmallSlot.value).prod : ℤ)) (Xm * ((hm.map SmallSlot.value).prod : ℤ)) := by
  have ht := localTests_of_supported_node hs hlarge
  have hprime : ∀ b ∈ u.map SmallSlot.value, Nat.Prime b := by
    intro b hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact ht.2.1 q hq
  have hcop : ∀ b ∈ u.map SmallSlot.value, IsCoprime a.frequency (b : ℤ) := by
    intro b hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    have hc := History.prime_coprime_small_frequency (ht.2.1 q hq)
      (History.supported_root_frequency_ne_zero hs)
      ((History.supported_root_frequency_bound hs).trans_lt (hlarge q hq))
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast, History.root] using hc.symm
  constructor
  · apply mul_ne_zero (History.supported_root_frequency_ne_zero hs)
    exact_mod_cast (History.supported_compensation_product_pos hs).ne'
  · apply (divisibility_iff (prime_list_pairwise ht.1 hprime) hcop).mpr
    refine ⟨hf, ?_⟩
    intro b hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact ho q hq

theorem pair_guardedOwnDivisibility_of_lines {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (Xp Xm : ℤ)
    (hx : ∀ i : Occurrences h k,
      AncestorUnits h k (fun j => (pairSample h k j : ZMod (slot h k i).value)) i)
    (hV : ∀ i : Occurrences h k, ∀ j ≤ l, V j < (slot h k i).value)
    (hlines : ∀ i : Occurrences h k, ((slot h k i).value : ℤ) ∣
      eval (pairSample h k) (leftFlag h k hs ks i) * Xp +
        eval (pairSample h k) (rightFlag h k hs ks i) * Xm) :
    GuardedOwnDivisibility h Xp Xm ∧ GuardedOwnDivisibility k Xp Xm := by
  have hactual (i : Occurrences h k) (hi : PairAncestorIntegralGuard h k Xp Xm i) :
      ((slot h k i).value : ℤ) ∣ pairActual h k Xp Xm i := by
    let : Fact (slot h k i).value.Prime := ⟨slot_prime h k hs ks i⟩
    have he := pairActual_power_dvd_iff_of_ancestorGuard h k hs ks hroot Xp Xm i hi
      (slot h k i).value 1 (hx i) (hV i)
    simp only [pow_one] at he
    exact he.mpr (hlines i)
  constructor
  · intro i hi
    exact hactual (Sum.inl i) hi
  · intro i hi
    exact hactual (Sum.inr i) hi

end Ostmann.Arithmetic.HistorySignedNumerators

end

end OAI
