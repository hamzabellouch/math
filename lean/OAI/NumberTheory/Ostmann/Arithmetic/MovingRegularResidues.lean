import OAI.NumberTheory.Ostmann.Construction.RegularGiantMultiplier
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullModulus

namespace OAI

/-! # Regular-prime multiplier coordinates in the actual full modulus -/

namespace Ostmann
open scoped BigOperators Classical

theorem movingRegularProduct_dvd_unitPeriod {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) :
    (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) ∣ movingGiantUnitPeriod value outside T := by
  cases T with
  | leaf s regular =>
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  | node s CL CR U left right =>
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) _) _

theorem movingFullPairModulus_regular_dvd {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) (b : Bool) (i : σ) (hi : i ∈ (T b).regularSlots) :
    value i ∣ movingFullPairModulus value hvalue outside childBound pivotBound T hf q S := by
  have hd : value i ∣ MovingSlotReversal.naturalProduct value (T b).regularSlots :=
    List.dvd_prod (List.mem_map.mpr ⟨i, hi, rfl⟩)
  have hdZ : (value i : ℤ) ∣ (MovingSlotReversal.naturalProduct value (T b).regularSlots : ℤ) := by exact_mod_cast hd
  have hu := (movingFullPairModulus_tests value hvalue outside childBound pivotBound T hf q S).2.2.1 b
  exact_mod_cast hdZ.trans ((movingRegularProduct_dvd_unitPeriod value outside (T b)).trans hu)

theorem guardedRegularMultiplier_full_modulus {σ I J : Type*} [Fintype J]
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) (p : J → ℕ) [∀ i, Fact (p i).Prime]
    (label : J → σ) (hp : ∀ i, value (label i) = p i)
    (hmem : ∀ i, label i ∈ (T false).regularSlots)
    (active : J → Bool) (s : ℤ) (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ)
    (XL XR : ℕ) :
    let M := movingFullPairModulus value hvalue outside childBound pivotBound T hf q S
    guardedRegularMultiplier p active s other g XL XR =
      guardedRegularMultiplier p active s other g (XL % M) (XR % M) := by
  dsimp only
  apply guardedRegularMultiplier_modEq
  · intro i
    rw [← hp i]
    exact movingFullPairModulus_regular_dvd value hvalue outside childBound pivotBound T hf q S false (label i) (hmem i)
  · exact (Nat.mod_modEq _ _).symm
  · exact (Nat.mod_modEq _ _).symm

end Ostmann

end OAI
