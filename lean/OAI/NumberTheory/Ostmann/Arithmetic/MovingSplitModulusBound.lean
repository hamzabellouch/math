import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularCoprime
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularResidues
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullModulusScale

namespace OAI

/-! # The split regular/auxiliary modulus retains the proved size bound -/

namespace Ostmann
open scoped BigOperators Classical

theorem movingSplitModulus_dvd_full {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) (R : ℕ)
    (hR : MovingSlotReversal.naturalProduct value (T false).regularSlots = R)
    (hcop : R.Coprime (movingReducedPairModulus value hvalue outside childBound pivotBound T hf q S)) :
    R * movingReducedPairModulus value hvalue outside childBound pivotBound T hf q S ∣
      movingFullPairModulus value hvalue outside childBound pivotBound T hf q S := by
  have hroot : R ∣ movingFullPairModulus value hvalue outside childBound pivotBound T hf q S := by
    rw [← hR]
    have hz := (movingRegularProduct_dvd_unitPeriod value outside (T false)).trans
      ((movingFullPairModulus_tests value hvalue outside childBound pivotBound T hf q S).2.2.1 false)
    exact_mod_cast hz
  exact hcop.mul_dvd_of_dvd_of_dvd hroot
    (movingReducedPairModulus_dvd_full value hvalue outside childBound pivotBound T hf q S)

theorem movingSplitModulus_bound {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (hout : outside.prod ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) (hq : ∀ i ∈ S, 0 < q i)
    (R : ℕ) (hR : MovingSlotReversal.naturalProduct value (T false).regularSlots = R)
    (hcop : R.Coprime (movingReducedPairModulus value hvalue outside childBound pivotBound T hf q S))
    (B : ℕ) (hB : 1 ≤ B) (hfreq : ∀ b, (T b).Frequencies (fun s => s.natAbs ≤ B))
    (hcomp : ∀ b, (T b).CompensationBound value B)
    (hregular : ∀ b, (T b).RegularBound value B) (houtB : outside.prod ≤ B) :
    R * movingReducedPairModulus value hvalue outside childBound pivotBound T hf q S ≤
      (B ^ movingFullModulusExponent n * ∏ i ∈ S, q i) ^ 4 := by
  exact (Nat.le_of_dvd
    (movingFullPairModulus_pos value hvalue outside hout childBound pivotBound T hf q S hq)
    (movingSplitModulus_dvd_full value hvalue outside childBound pivotBound T hf q S R hR hcop)).trans
    (movingFullPairModulus_bound value hvalue outside childBound pivotBound T hf q S B hB hfreq hcomp hregular houtB)

end Ostmann

end OAI
