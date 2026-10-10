import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedModulus

namespace OAI

/-! # The CRT split for the actual common regular slots -/

namespace Ostmann
open scoped Classical

private theorem product_coprime_frequency {σ : Type*} (value : σ → ℕ) (L : List σ) (s : ℤ)
    (h : ∀ i, IsCoprime s (value i : ℤ)) :
    (MovingSlotReversal.naturalProduct value L).Coprime s.natAbs := by
  apply Nat.coprime_list_prod_left_iff.mpr
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  simpa only [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using (h i).symm

theorem MovingSlotData.smallProduct_frequency_coprime {σ : Type*} (value : σ → ℕ)
    (L : List σ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ))) :
    T.Frequencies (fun s => (MovingSlotReversal.naturalProduct value L).Coprime s.natAbs) := by
  induction T with
  | leaf s regular => exact product_coprime_frequency value L s hf
  | node s CL CR U left right ihL ihR =>
    exact ⟨product_coprime_frequency value L s (fun i => (hf i).1),
      ihL (fun i => (hf i).2.1), ihR (fun i => (hf i).2.2)⟩

/-- For the two original histories, the computed reduced modulus is coprime
to their common regular-prime product. No extra coprimality of moduli is assumed. -/
theorem movingOriginalRegular_coprime_reduced {σ I : Type*} (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hlevels : ∀ b, (T b).Levels tier)
    (hsmall : ∀ b i, (T b).Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hout : ∀ b, movingRegularOutsidePairwise value outside (T b))
    (R : ℕ) (hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = R)
    (q : I → ℕ) (S : Finset I) (hq : ∀ i ∈ S, R.Coprime (q i)) :
    R.Coprime (movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside
      childBound pivotBound T hf q S) := by
  apply movingReducedPairModulus_coprime value (fun i => (hprime i).ne_zero)
    outside childBound pivotBound T hf q S R _ _ hq
  · intro b
    have h := (T b).smallProduct_frequency_coprime value (T false).regularSlots (hsmall b)
    simpa only [hregular false] using h
  · intro b
    have h := movingRegularProduct_coprime_auxiliary tier value hprime hdisjoint outside
      (T b) (hlevels b) (hsmall b) (hout b)
    simpa only [hregular b, Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using h

end Ostmann

end OAI
