import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkProducts
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyResidues
import OAI.NumberTheory.Ostmann.Characters.TemplateFrequencyConstraint

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts Characters
open Characters.Template (unitConvention unitConvention_coe)

def coefficientUnit (s : ℤ) (X : ℕ) (xs : List SmallSlot) : (ZMod s.natAbs)ˣ :=
  unitConvention ((X*fixedProduct xs:ℕ):ZMod s.natAbs)

def bulkUnit (s : ℤ) (xs : List SmallSlot) : (ZMod s.natAbs)ˣ :=
  unitConvention (bulkProduct xs:ZMod s.natAbs)

theorem fixedProduct_coprime {s : ℤ} {xs : List SmallSlot}
    (hc : ∀ q∈xs,Nat.Coprime q.value s.natAbs) : Nat.Coprime (fixedProduct xs) s.natAbs := by
  apply Nat.coprime_list_prod_left_iff.mpr
  intro n hn
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hn
  exact hc q (List.mem_filter.mp hq).1

theorem bulkProduct_coprime {s : ℤ} {xs : List SmallSlot}
    (hc : ∀ q∈xs,Nat.Coprime q.value s.natAbs) : Nat.Coprime (bulkProduct xs) s.natAbs := by
  apply Nat.coprime_list_prod_left_iff.mpr
  intro n hn
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hn
  exact hc q (List.mem_filter.mp hq).1

theorem coefficientUnit_coe (s : ℤ) (X : ℕ) (xs : List SmallSlot)
    (hX : Nat.Coprime X s.natAbs) (hc : ∀ q∈xs,Nat.Coprime q.value s.natAbs) :
    (coefficientUnit s X xs:ZMod s.natAbs)=(X:ZMod s.natAbs)*(fixedProduct xs:ZMod s.natAbs) := by
  simpa only [coefficientUnit,Nat.cast_mul] using unitConvention_coe
    ((X*fixedProduct xs:ℕ):ZMod s.natAbs)
    ((ZMod.isUnit_iff_coprime _ _).mpr (hX.mul_left (fixedProduct_coprime hc)))

theorem bulkUnit_coe (s : ℤ) (xs : List SmallSlot)
    (hc : ∀ q∈xs,Nat.Coprime q.value s.natAbs) :
    (bulkUnit s xs:ZMod s.natAbs)=(bulkProduct xs:ZMod s.natAbs) :=
  unitConvention_coe _ ((ZMod.isUnit_iff_coprime _ _).mpr (bulkProduct_coprime hc))

theorem rawSplit_of_integrality (s v w : ℤ) (Xplus Xminus : ℕ) (hp hm : List SmallSlot)
    (hXplus : Nat.Coprime Xplus s.natAbs) (hXminus : Nat.Coprime Xminus s.natAbs)
    (hhp : ∀ q∈hp,Nat.Coprime q.value s.natAbs) (hhm : ∀ q∈hm,Nat.Coprime q.value s.natAbs)
    (hint : s∣reversalNumerator v w ((Xplus*(hp.map SmallSlot.value).prod:ℕ):ℤ)
      ((Xminus*(hm.map SmallSlot.value).prod:ℕ):ℤ)) :
    rawSplitConstraint s.natAbs v w (coefficientUnit s Xplus hp) (coefficientUnit s Xminus hm)
      (bulkUnit s hp*bulkUnit s hm) (bulkUnit s hp) := by
  have hz : ((reversalNumerator v w ((Xplus*(hp.map SmallSlot.value).prod:ℕ):ℤ)
      ((Xminus*(hm.map SmallSlot.value).prod:ℕ):ℤ) : ℤ):ZMod s.natAbs)=0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    simpa only [Int.natCast_natAbs,abs_dvd] using hint
  simp only [reversalNumerator,product_split,Nat.cast_mul,Int.cast_sub,Int.cast_mul,Int.cast_natCast] at hz
  unfold rawSplitConstraint
  rw [mul_div_cancel_left,coefficientUnit_coe s Xplus hp hXplus hhp,
    coefficientUnit_coe s Xminus hm hXminus hhm,bulkUnit_coe s hp hhp,bulkUnit_coe s hm hhm]
  exact sub_eq_zero.mp (by simpa only [mul_assoc] using hz)

theorem supported_rawSplit {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {comp hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p comp hp hm left right).Supported V outside)
    (hsize : ∀ q∈a.small,V (l+1)<q.value) :
    rawSplitConstraint a.frequency.natAbs left.root.frequency right.root.frequency
      (coefficientUnit a.frequency a.giantPlus hp) (coefficientUnit a.frequency a.giantMinus hm)
      (bulkUnit a.frequency hp*bulkUnit a.frequency hm) (bulkUnit a.frequency hp) := by
  have hzero := History.supported_root_frequency_ne_zero hs
  have hbound := History.supported_root_frequency_bound hs
  have hprime : a.PrimeSmall := by rw [History.Supported.eq_def] at hs; exact hs.2.1
  have hg : (History.node a p comp hp hm left right).GiantUnits := by
    rw [History.Supported.eq_def] at hs
    exact hs.2.2.2.2.2.2.1
  have hgiants := hg a.frequency List.mem_cons_self
  have hsmall : ∀ q∈a.small,Nat.Coprime q.value a.frequency.natAbs := by
    intro q hq
    exact History.prime_coprime_small_frequency (hprime q hq) hzero (hbound.trans_lt (hsize q hq))
  have hperm := History.supported_small_split hs
  apply rawSplit_of_integrality _ _ _ _ _ _ _ hgiants.1 hgiants.2
    (fun q hq => hsmall q (hperm.mem_iff.mpr (List.mem_append_left hm hq)))
    (fun q hq => hsmall q (hperm.mem_iff.mpr (List.mem_append_right hp hq)))
  exact ⟨(comp.map SmallSlot.value).prod*p,by
    simpa only [History.root,Nat.cast_mul,mul_assoc] using History.supported_reversal hs⟩

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
