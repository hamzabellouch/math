import OAI.NumberTheory.Ostmann.Arithmetic.MovingCoprimePeriods
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullModulus

namespace OAI

/-! # The common residue modulus after extracting the regular primes -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def movingReducedPairModulusBase {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) : ℕ :=
  ∏ b : Bool, movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S *
    (movingAuxiliaryUnitPeriod value outside (T b)).natAbs

noncomputable def movingReducedPairModulus {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) : ℕ :=
  (movingReducedPairModulusBase value hvalue outside childBound pivotBound T hf q S) ^ 2

theorem movingReducedPairModulus_components {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) (b : Bool) :
    movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S ∣
      movingReducedPairModulusBase value hvalue outside childBound pivotBound T hf q S ∧
    (movingAuxiliaryUnitPeriod value outside (T b)).natAbs ∣
      movingReducedPairModulusBase value hvalue outside childBound pivotBound T hf q S := by
  have h := Finset.dvd_prod_of_mem
    (fun b => movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S *
      (movingAuxiliaryUnitPeriod value outside (T b)).natAbs) (Finset.mem_univ b)
  exact ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩

theorem movingReducedPairModulus_pos {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (hout : outside.prod ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) (hq : ∀ i ∈ S, 0 < q i) :
    0 < movingReducedPairModulus value hvalue outside childBound pivotBound T hf q S := by
  apply pow_pos
  apply Finset.prod_pos
  intro b _
  exact Nat.mul_pos (movingSpectatorModulus_pos value hvalue childBound pivotBound (T b) (hf b) q S hq)
    (Int.natAbs_pos.mpr ((ne_zero_of_dvd_ne_zero (movingGiantUnitPeriod_ne_zero value hvalue outside hout (T b) (hf b)) (movingAuxiliaryUnitPeriod_dvd_full value outside (T b)))))

/-- The one common modulus supplies all four divisibility conditions used in
exact two-history factorization, including every compensation-prime square. -/
theorem movingReducedPairModulus_tests {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) :
    let M := movingReducedPairModulus value hvalue outside childBound pivotBound T hf q S
    (∀ b, movingTopPeriod value hvalue childBound pivotBound (T b) (hf b) ∣ M) ∧
    (∀ b, ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value (T b) ∣ (M : ℤ)) ∧
    (∀ b, movingAuxiliaryUnitPeriod value outside (T b) ∣ (M : ℤ)) ∧
    (∀ b, ∀ o ∈ (T b).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ (M : ℤ)) := by
  let N := movingReducedPairModulusBase value hvalue outside childBound pivotBound T hf q S
  have hN : N ∣ N ^ 2 := ⟨N, pow_two N⟩
  have hc := movingReducedPairModulus_components value hvalue outside childBound pivotBound T hf q S
  have hs (b : Bool) : movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S ∣ N ^ 2 :=
    (hc b).1.trans hN
  refine ⟨fun b => (movingTopPeriod_dvd_spectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S).trans (hs b),
    fun b i hi => ?_, fun b => ?_, fun b o ho i hi => ?_⟩
  · exact (spectator_dvd_movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S i hi).trans
      (by exact_mod_cast hs b)
  · exact (Int.dvd_natAbs.mpr (dvd_refl (movingAuxiliaryUnitPeriod value outside (T b)))).trans
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

/-- The reduced modulus introduces no new size cost. -/
theorem movingReducedPairModulus_dvd_full {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) :
    movingReducedPairModulus value hvalue outside childBound pivotBound T hf q S ∣
      movingFullPairModulus value hvalue outside childBound pivotBound T hf q S := by
  apply pow_dvd_pow_of_dvd
  apply Finset.prod_dvd_prod_of_dvd
  intro b _
  exact Nat.mul_dvd_mul_left _ (Int.natAbs_dvd_natAbs.mpr
    (movingAuxiliaryUnitPeriod_dvd_full value outside (T b)))

/-- The auxiliary period and the node frequencies suffice to split off any
regular block coprime to the fixed spectator primes. -/
theorem movingReducedPairModulus_coprime {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) (r : ℕ)
    (hfreq : ∀ b, (T b).Frequencies (fun s => r.Coprime s.natAbs))
    (haux : ∀ b, r.Coprime (movingAuxiliaryUnitPeriod value outside (T b)).natAbs)
    (hq : ∀ i ∈ S, r.Coprime (q i)) :
    r.Coprime (movingReducedPairModulus value hvalue outside childBound pivotBound T hf q S) := by
  apply Nat.Coprime.pow_right
  apply Nat.coprime_prod_right_iff.mpr
  intro b _
  have ht := movingTopPeriod_coprime_of_auxiliary value hvalue outside childBound pivotBound
    (T b) (hf b) r (hfreq b) (haux b)
  have hd := (haux b).of_dvd_right (Int.natAbs_dvd_natAbs.mpr
    (movingSpectatorDenominator_dvd_auxiliary value outside (T b)))
  exact (((ht.mul_right hd).mul_right (Nat.coprime_prod_right_iff.mpr hq)).mul_right (haux b))

end Ostmann

end OAI
