import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.ChargePenalty

namespace OAI

/-!
# Exact energy of a virtual hole and double occupancy

A single hop out of the singly occupied subspace creates one empty site and
one doubly occupied site. The full long-range charge penalty on that
configuration is exactly `U - V i j`, so intersite direct repulsion remains
in the superexchange denominator.
-/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def chargeTransferOccupation {m : ℕ} (hole double : Fin m) : Fin m → Fin 3 :=
  Function.update (Function.update (fun _ => 1) hole 0) double 2

theorem chargeTransfer_deviation {m : ℕ} (hole double k : Fin m) (hne : hole ≠ double) :
    occupationDeviation (chargeTransferOccupation hole double) k =
      (if k = double then (1 : ℝ) else 0) - (if k = hole then (1 : ℝ) else 0) := by
  by_cases hkh : k = hole
  · subst k
    norm_num [chargeTransferOccupation, occupationDeviation, hne]
  · by_cases hkd : k = double
    · subst k
      norm_num [chargeTransferOccupation, occupationDeviation, hne.symm]
    · norm_num [chargeTransferOccupation, occupationDeviation, hkh, hkd]

theorem chargeTransfer_weighted_sum {m : ℕ} (hole double : Fin m) (hne : hole ≠ double)
    (f : Fin m → ℝ) :
    (∑ k, f k * occupationDeviation (chargeTransferOccupation hole double) k) =
      f double - f hole := by
  simp only [chargeTransfer_deviation hole double _ hne, mul_sub,
    Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  simp

theorem chargeTransfer_deviation_sq_sum {m : ℕ} (hole double : Fin m) (hne : hole ≠ double) :
    (∑ k, occupationDeviation (chargeTransferOccupation hole double) k ^ 2) = 2 := by
  have hpoint (k : Fin m) : occupationDeviation (chargeTransferOccupation hole double) k ^ 2 =
      (if k = double then (1 : ℝ) else 0) + (if k = hole then (1 : ℝ) else 0) := by
    rw [chargeTransfer_deviation hole double k hne]
    by_cases hkh : k = hole
    · subst k
      norm_num [hne]
    · by_cases hkd : k = double <;> norm_num [hkh, hkd, hne.symm]
  simp_rw [hpoint, Finset.sum_add_distrib]
  norm_num

/-- All direct interactions except the hole-double interaction cancel. -/
theorem chargeTransfer_penalty {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ)
    (hole double : Fin m) (hne : hole ≠ double)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0) :
    chargePenalty U V (chargeTransferOccupation hole double) = U - V hole double := by
  let d := occupationDeviation (chargeTransferOccupation hole double)
  have hinner (k : Fin m) : (∑ l, V k l * d l) = V k double - V k hole :=
    chargeTransfer_weighted_sum hole double hne (V k)
  have hquad : (∑ k, ∑ l, V k l * d k * d l) = -2 * V hole double := by
    calc
      _ = ∑ k, (V k double - V k hole) * d k := by
        apply Finset.sum_congr rfl
        intro k _
        calc
          _ = (∑ l, V k l * d l) * d k := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro l _
            ring
          _ = _ := by rw [hinner]
      _ = (V double double - V double hole) - (V hole double - V hole hole) :=
        chargeTransfer_weighted_sum hole double hne (fun k => V k double - V k hole)
      _ = _ := by rw [hdiag, hdiag, hsymm double hole]; ring
  unfold chargePenalty
  rw [chargeTransfer_deviation_sq_sum hole double hne]
  change U / 2 * 2 + (1 / 2 : ℝ) * (∑ k, ∑ l, V k l * d k * d l) = _
  rw [hquad]
  ring

end ContinuumCoulomb

end

end OAI
