import OAI.NumberTheory.Ostmann.Arithmetic.MovingAuxiliaryPeriod
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSmallFrequencyUnits

namespace OAI

/-! # The recursive auxiliary period is coprime to the original regular block -/

namespace Ostmann
open scoped Classical

private theorem product_coprime_right {σ : Type*} (value : σ → ℕ) (p : ℤ)
    (L : List σ) (h : ∀ i ∈ L, IsCoprime p (value i : ℤ)) :
    IsCoprime p (MovingSlotReversal.naturalProduct value L : ℤ) := by
  induction L with
  | nil => simpa [MovingSlotReversal.naturalProduct] using (isCoprime_one_right (x := p))
  | cons a L ih =>
    simpa only [MovingSlotReversal.naturalProduct, List.map_cons, List.prod_cons, Nat.cast_mul]
      using (h a List.mem_cons_self).mul_right (ih (fun i hi => h i (List.mem_cons_of_mem a hi)))

theorem MovingSlotData.regular_level_bound {σ : Type*} (tier : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hT : T.Levels tier) (i : σ) (hi : i ∈ T.regularSlots) : n ≤ tier i := by
  cases T with
  | leaf => exact Nat.zero_le _
  | node s CL CR U left right =>
    exact (List.mem_append.mp hi).elim (hT.1 i) (hT.2.1 i)

theorem movingAuxiliaryUnitPeriod_coprime {σ : Type*} (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (hT : T.Levels tier)
    (i : σ) (hi : n ≤ tier i)
    (hf : T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (ho : IsCoprime (value i : ℤ) (outside.prod : ℤ)) :
    IsCoprime (value i : ℤ) (movingAuxiliaryUnitPeriod value outside T) := by
  induction T with
  | leaf s regular => exact hf.symm.mul_right ho
  | @node n s CL CR U left right ihL ihR =>
    have hcomp : IsCoprime (value i : ℤ) (MovingSlotReversal.naturalProduct value U : ℤ) := by
      apply product_coprime_right
      intro j hj
      have hneq : value i ≠ value j := hdisjoint i j (by have := hT.2.2.1 j hj; omega)
      exact ((Nat.coprime_primes (hprime i) (hprime j)).mpr hneq).isCoprime
    have hfreq : IsCoprime (value i : ℤ)
        (MovingSlotData.node s CL CR U left right).frequencyProduct :=
      ((MovingSlotData.node s CL CR U left right).frequencies_isCoprime _).mp
        (hf.mono (fun _ h => h.symm))
    exact (((hfreq.mul_right ho).mul_right (hf.1.symm.mul_right hcomp)).mul_right
      (ihL hT.2.2.2.1 (by omega) hf.2.1)).mul_right (ihR hT.2.2.2.2 (by omega) hf.2.2)

/-- This is the actual CRT separation: an original regular prime has higher
level than every compensation prime in the subtree, and is coprime to every
frequency and to the fixed outside list. -/
theorem movingRegularProduct_coprime_auxiliary {σ : Type*} (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (hT : T.Levels tier)
    (hf : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (houtside : movingRegularOutsidePairwise value outside T) :
    IsCoprime (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ)
      (movingAuxiliaryUnitPeriod value outside T) := by
  have hroot : (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime := by
    cases T with
    | leaf => exact houtside
    | node => exact houtside.1
  have hp : (MovingSlotReversal.naturalProduct value T.regularSlots).Coprime
      (movingAuxiliaryUnitPeriod value outside T).natAbs := by
    apply Nat.coprime_list_prod_left_iff.mpr
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    have ho : (value i).Coprime outside.prod := by
      apply Nat.coprime_list_prod_right_iff.mpr
      intro b hb
      exact (List.pairwise_append.mp hroot).2.2 _ (List.mem_map.mpr ⟨i, hi, rfl⟩) b hb
    have h := movingAuxiliaryUnitPeriod_coprime tier value hprime hdisjoint outside T hT i
      (T.regular_level_bound tier hT i hi) (hf i) ho.isCoprime
    simpa only [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using h
  simpa only [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using hp

end Ostmann

end OAI
