import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternRegularSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSmallFrequencyUnits

namespace OAI

/-! # The actual regular Fourier denominators are units on the original support -/

namespace Ostmann
open scoped Classical BigOperators

/-- The denominator left after removing one regular prime and both giants. -/
noncomputable def movingRegularOther {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (slots : List σ) (j : Fin slots.length) : ℤ :=
  (outside.prod * ∏ i ∈ Finset.univ.erase j, value (slots.get i) : ℕ)

theorem movingPattern_regular_other_unit {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C) (value : Fin (N + 1) → ℕ)
    (hprime : ∀ i, (value i).Prime) (outside : List ℕ) (b : Bool)
    (h : movingRegularOutsidePairwise value outside
      (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern b))
    (j : Fin (movingPatternRegularSlots e n m small slot).length) :
    (movingRegularOther value outside (movingPatternRegularSlots e n m small slot) j :
      ZMod (value ((movingPatternRegularSlots e n m small slot).get j))) ≠ 0 := by
  let slots := movingPatternRegularSlots e n m small slot
  let : Fact (value (slots.get j)).Prime := ⟨hprime _⟩
  have hp : (((movingPatternFinBulkData e n m t (fun _ => small) slot
      (Equiv.refl _) pattern b).regularSlots.map value) ++ outside).Pairwise Nat.Coprime := by
    cases ht : movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern b with
    | leaf => exact ht ▸ h
    | node => exact (ht ▸ h).1
  have hperm := ((movingPatternFinBulkData_regular_perm e t small slot pattern b).map value).append_right outside
  have hc : (slots.map value ++ outside).Pairwise Nat.Coprime :=
    (hperm.pairwise_iff (R := Nat.Coprime) (fun h => h.symm)).mp hp
  have ho : (value (slots.get j)).Coprime outside.prod := by
    apply Nat.coprime_list_prod_right_iff.mpr
    intro q hq
    exact (List.pairwise_append.mp hc).2.2 _
      (List.mem_map.mpr ⟨slots.get j, List.get_mem slots j, rfl⟩) q hq
  have hr := movingPattern_regular_pairwise e t small slot pattern value outside b h
  have hrest : (value (slots.get j)).Coprime
      (∏ i ∈ Finset.univ.erase j, value (slots.get i)) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro i hi
    exact hr (Finset.ne_of_mem_erase hi).symm
  have hu := (ZMod.isUnit_iff_coprime _ (value (slots.get j))).mpr (ho.mul_right hrest).symm
  simpa only [movingRegularOther, Int.cast_natCast] using hu.ne_zero

/-- Every retained frequency is a unit at a regular prime above the common cutoff. -/
theorem movingPattern_regular_frequency_unit {σ : Type*}
    (value : σ → ℕ) (hprime : ∀ i, (value i).Prime) (slots : List σ)
    (V : ℕ) (hlarge : ∀ i, V < value i) (s : ℤ) (hs : s ≠ 0) (hV : s.natAbs ≤ V)
    (j : Fin slots.length) : (s : ZMod (value (slots.get j))) ≠ 0 := by
  let : Fact (value (slots.get j)).Prime := ⟨hprime _⟩
  have hc := small_prime_frequency_unit (value (slots.get j)) (hprime (slots.get j)) s hs
    (hV.trans_lt (hlarge (slots.get j)))
  have hu : IsUnit (s : ZMod (value (slots.get j))) := by
    apply isCoprime_zero_right.mp
    simpa only [Int.cast_natCast, ZMod.natCast_self] using
      hc.intCast (R := ZMod (value (slots.get j)))
  exact hu.ne_zero

end Ostmann

end OAI
