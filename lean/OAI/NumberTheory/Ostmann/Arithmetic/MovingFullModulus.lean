import OAI.NumberTheory.Ostmann.Arithmetic.MovingUnitSampleBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorModulus

namespace OAI

/-! # A concrete common modulus for every full-support residue test -/

namespace Ostmann
open scoped BigOperators Classical

theorem MovingSlotData.compensation_dvd_spectatorDenominator {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) :
    ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots,
      (value i : ℤ) ∣ movingSpectatorDenominator value T := by
  induction T with
  | leaf => simp [occurrences]
  | node s CL CR U left right ihL ihR =>
    intro o ho i hi
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      have hd : value i ∣ MovingSlotReversal.naturalProduct value U :=
        List.dvd_prod (List.mem_map.mpr ⟨i, hi, rfl⟩)
      have hz : (value i : ℤ) ∣ (MovingSlotReversal.naturalProduct value U : ℤ) := by exact_mod_cast hd
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hz s) _) _
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (ihL o' ho' i hi) _) _
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        exact dvd_mul_of_dvd_right (ihR o' ho' i hi) _

noncomputable def movingFullPairModulusBase {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) : ℕ :=
  ∏ b : Bool, movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S *
    (movingGiantUnitPeriod value outside (T b)).natAbs

noncomputable def movingFullPairModulus {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) : ℕ :=
  (movingFullPairModulusBase value hvalue outside childBound pivotBound T hf q S) ^ 2

theorem movingFullPairModulus_components {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) (b : Bool) :
    movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S ∣
      movingFullPairModulusBase value hvalue outside childBound pivotBound T hf q S ∧
    (movingGiantUnitPeriod value outside (T b)).natAbs ∣
      movingFullPairModulusBase value hvalue outside childBound pivotBound T hf q S := by
  have h := Finset.dvd_prod_of_mem
    (fun b => movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S *
      (movingGiantUnitPeriod value outside (T b)).natAbs) (Finset.mem_univ b)
  exact ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩

theorem movingFullPairModulus_pos {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (hout : outside.prod ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) (hq : ∀ i ∈ S, 0 < q i) :
    0 < movingFullPairModulus value hvalue outside childBound pivotBound T hf q S := by
  apply pow_pos
  apply Finset.prod_pos
  intro b _
  exact Nat.mul_pos (movingSpectatorModulus_pos value hvalue childBound pivotBound (T b) (hf b) q S hq)
    (Int.natAbs_pos.mpr (movingGiantUnitPeriod_ne_zero value hvalue outside hout (T b) (hf b)))

/-- The one common modulus supplies all four divisibility conditions used in
exact two-history factorization, including every compensation-prime square. -/
theorem movingFullPairModulus_tests {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) :
    let M := movingFullPairModulus value hvalue outside childBound pivotBound T hf q S
    (∀ b, movingTopPeriod value hvalue childBound pivotBound (T b) (hf b) ∣ M) ∧
    (∀ b, ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value (T b) ∣ (M : ℤ)) ∧
    (∀ b, movingGiantUnitPeriod value outside (T b) ∣ (M : ℤ)) ∧
    (∀ b, ∀ o ∈ (T b).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ (M : ℤ)) := by
  let N := movingFullPairModulusBase value hvalue outside childBound pivotBound T hf q S
  have hN : N ∣ N ^ 2 := ⟨N, pow_two N⟩
  have hc := movingFullPairModulus_components value hvalue outside childBound pivotBound T hf q S
  have hs (b : Bool) : movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S ∣ N ^ 2 :=
    (hc b).1.trans hN
  refine ⟨fun b => (movingTopPeriod_dvd_spectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S).trans (hs b),
    fun b i hi => ?_, fun b => ?_, fun b o ho i hi => ?_⟩
  · exact (spectator_dvd_movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S i hi).trans
      (by exact_mod_cast hs b)
  · exact (Int.dvd_natAbs.mpr (dvd_refl (movingGiantUnitPeriod value outside (T b)))).trans
      (by exact_mod_cast (hc b).2.trans hN)
  · have hd : value i ∣ (movingSpectatorDenominator value (T b)).natAbs := by
      exact_mod_cast Int.dvd_natAbs.mpr ((T b).compensation_dvd_spectatorDenominator value o ho i hi)
    have hds : (movingSpectatorDenominator value (T b)).natAbs ∣
        movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S := by
      refine ⟨movingTopPeriod value hvalue childBound pivotBound (T b) (hf b) * ∏ j ∈ S, q j, ?_⟩
      simp only [movingSpectatorModulus]
      ring
    have hpow := pow_dvd_pow_of_dvd (hd.trans (hds.trans (hc b).1)) 2
    exact_mod_cast hpow

end Ostmann

end OAI
