import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencySplit
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReductionBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts Characters HistorySupportReduction HistorySignedDecode

theorem node_half_frequency_units {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hlarge : ∀q∈a.small,V (l+1)<q.value) :
    (∀q∈hp,Nat.Coprime q.value a.frequency.natAbs) ∧
      (∀q∈hm,Nat.Coprime q.value a.frequency.natAbs) := by
  have hprime : a.PrimeSmall := (rootData_of_supported hs).2.1
  have hu : ∀q∈a.small,Nat.Coprime q.value a.frequency.natAbs := by
    intro q hq
    exact History.prime_coprime_small_frequency (hprime q hq)
      (History.supported_root_frequency_ne_zero hs)
      ((History.supported_root_frequency_bound hs).trans_lt (hlarge q hq))
  have hperm := History.supported_small_split hs
  exact ⟨fun q hq => hu q (hperm.mem_iff.mpr (List.mem_append_left hm hq)),
    fun q hq => hu q (hperm.mem_iff.mpr (List.mem_append_right hp hq))⟩

theorem signed_node_frequency_iff_of_eq
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
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
  have hu := node_half_frequency_units hs hlarge
  exact signed_known_rawSplit_iff a.frequency left.root.frequency right.root.frequency
    Xp Xm hp hm R K j hf g hg x y hx hy hXp hXm hu.1 hu.2

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
