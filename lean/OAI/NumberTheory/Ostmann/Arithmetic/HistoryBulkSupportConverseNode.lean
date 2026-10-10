import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSkeleton

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistoryBulkProducts Characters HistorySupportReduction HistorySignedDecode
open HistoryFrequencyResidues HistorySignedNumerators HistorySupportDescent

theorem node_half_frequency_units_static {l : ℕ} {V : ℕ → ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : StaticSkeleton V (History.node a p u hp hm left right))
    (hlarge : ∀q∈a.small,V (l+1)<q.value) :
    (∀q∈hp,Nat.Coprime q.value a.frequency.natAbs) ∧
      (∀q∈hm,Nat.Coprime q.value a.frequency.natAbs) := by
  have hprime : a.PrimeSmall := hs.1.primeSmall
  have hu : ∀q∈a.small,Nat.Coprime q.value a.frequency.natAbs := by
    intro q hq
    exact History.prime_coprime_small_frequency (hprime q hq)
      hs.1.frequency_ne_zero
      (hs.1.frequency_bound.trans_lt (hlarge q hq))
  have hperm := hs.2.1.split
  exact ⟨fun q hq => hu q (hperm.mem_iff.mpr (List.mem_append_left hm hq)),
    fun q hq => hu q (hperm.mem_iff.mpr (List.mem_append_right hp hq))⟩

theorem signed_node_frequency_iff_of_eq_static
    {l : ℕ} {V : ℕ → ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : StaticSkeleton V (History.node a p u hp hm left right))
    (hlarge : ∀q∈a.small,V (l+1)<q.value)
    (R K j : ℕ) (s : ℤ) (hf : s.natAbs∣R) (he : s=a.frequency)
    (g : KnownGiants R) (Xp Xm : ℤ) (hg : SignedGiantsMatch R j g Xp Xm)
    (hXp : IsUnit (Xp:ZMod a.frequency.natAbs)) (hXm : IsUnit (Xm:ZMod a.frequency.natAbs))
    (x y : (ZMod (R^(K+2)))ˣ)
    (hx : (bulkProduct hp:ZMod (R^(K+2)))=x)
    (hy : (bulkProduct hm:ZMod (R^(K+2)))=y) :
    rawSplitConstraint s.natAbs left.root.frequency right.root.frequency
      (knownCoefficient R j s hf (fixedProduct hp) (g j).1)
      (knownCoefficient R j s hf (fixedProduct hm) (g j).2)
      (ZMod.unitsMap (Template.frequency_dvd_precision R K hf) (x*y))
      (ZMod.unitsMap (Template.frequency_dvd_precision R K hf) x) ↔
      a.frequency ∣ reversalNumerator left.root.frequency right.root.frequency
        (Xp*((hp.map SmallSlot.value).prod:ℤ)) (Xm*((hm.map SmallSlot.value).prod:ℤ)) := by
  subst s
  have hu := node_half_frequency_units_static hs hlarge
  exact signed_known_rawSplit_iff a.frequency left.root.frequency right.root.frequency
    Xp Xm hp hm R K j hf g hg x y hx hy hXp hXm hu.1 hu.2

variable {l : ℕ} {a : State} {p : ℕ} {u hp hm : List SmallSlot}
  {left right : History l}

theorem node_integral_of_frequency_and_own_static {V : ℕ → ℕ}
    (hs : StaticSkeleton V (History.node a p u hp hm left right))
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
  have hprime : ∀ b ∈ u.map SmallSlot.value, Nat.Prime b := by
    intro b hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact hs.2.1.primeComp q hq
  have hcop : ∀ b ∈ u.map SmallSlot.value, IsCoprime a.frequency (b : ℤ) := by
    intro b hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    have hc := History.prime_coprime_small_frequency (hs.2.1.primeComp q hq)
      hs.1.frequency_ne_zero
      (hs.1.frequency_bound.trans_lt (hlarge q hq))
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast, History.root] using hc.symm
  constructor
  · apply mul_ne_zero hs.1.frequency_ne_zero
    have hpos : 0 < (u.map SmallSlot.value).prod := by
      apply List.prod_pos
      intro q hq
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
      exact (hs.2.1.primeComp b hb).pos
    exact_mod_cast hpos.ne' 
  · apply (divisibility_iff (prime_list_pairwise hs.2.1.distinctComp hprime) hcop).mpr
    refine ⟨hf, ?_⟩
    intro b hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact ho q hq

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
