import OAI.NumberTheory.JointDickman.Amplification.ReducedArcLifts
import OAI.NumberTheory.JointDickman.Probability.FiniteKernelOrthogonality
import OAI.NumberTheory.JointDickman.Counting.OscillatoryCoefficientLaw
import OAI.NumberTheory.JointDickman.Arithmetic.SmoothCoefficientMinorArc

namespace OAI

/-! # The exact coefficient phase on a lifted major arc -/

namespace JointDickman
open Finset

theorem additivePhase_int (k : ℤ) : additivePhase (k : ℝ) = 1 := by
  unfold additivePhase
  have he : ((2*Real.pi*(k : ℝ) : ℝ) : ℂ)*Complex.I =
      (k : ℂ)*(2*(Real.pi : ℂ)*Complex.I) := by push_cast; ring
  rw [he,Complex.exp_int_mul_two_pi_mul_I]

theorem additivePhase_add_int (x : ℝ) (k : ℤ) : additivePhase (x+k) = additivePhase x := by
  rw [additivePhase_add,additivePhase_int,mul_one]

theorem finiteAdditiveSum_add_int (s : Finset ℕ) (c : ℕ → ℂ) (θ : ℝ) (k : ℤ) :
    finiteAdditiveSum s c (θ+k) = finiteAdditiveSum s c θ := by
  unfold finiteAdditiveSum
  apply sum_congr rfl
  intro n _
  have he : (n : ℝ)*(θ+k) = n*θ+((n : ℤ)*k : ℤ) := by push_cast; ring
  rw [he,additivePhase_add_int]

theorem finiteAdditiveSum_periodic (s : Finset ℕ) (c : ℕ → ℂ) :
    Function.Periodic (finiteAdditiveSum s c) 1 := by
  intro θ
  simpa only [Int.cast_one] using finiteAdditiveSum_add_int s c θ 1

theorem lifted_arc_coefficient_phase {j q : ℕ} [NeZero j] [NeZero q] [NeZero (j*q)]
    (t : Fin j) (r : Fin q) {X : ℝ} (hX : X ≠ 0) (ξ : ℝ)
    (C : Finset ℕ) (c : ℕ → ℂ) :
    finiteAdditiveSum C c (-(j : ℝ)*
      (((arcLiftEquiv j q (t,r)).val : ℝ)/(j*q : ℕ)+ξ/((j : ℝ)*X))) =
      finiteAdditiveSum C c (-(r.val : ℝ)/q-ξ/X) := by
  have hj : (j : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne j
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [arcLiftEquiv_location]
  have he : -(j : ℝ)*(((r.val : ℝ)/q+t.val)/j+ξ/((j : ℝ)*X)) =
      (-(r.val : ℝ)/q-ξ/X)+(-(t.val : ℤ) : ℤ) := by
    push_cast
    field_simp
    ring
  rw [he,finiteAdditiveSum_add_int]

theorem coefficientExponentialSum_eq_smooth (B q : ℕ) [NeZero q]
    (u : (ZMod q)ˣ) (ξ X : ℝ) (w : ℝ → ℝ) :
    coefficientExponentialSum B q u ξ X w =
      smoothCoefficientAdditiveSum B X (((u : ZMod q).val : ℝ)/q+ξ/X) w := by
  unfold coefficientExponentialSum smoothCoefficientAdditiveSum
  apply tsum_congr
  intro n
  congr 2
  ring

theorem coefficientExponentialSum_neg_unit (B q : ℕ) [NeZero q]
    (u : (ZMod q)ˣ) (ξ X : ℝ) (w : ℝ → ℝ) :
    coefficientExponentialSum B q (-u) ξ X w =
      smoothCoefficientAdditiveSum B X (-((u : ZMod q).val : ℝ)/q+ξ/X) w := by
  unfold coefficientExponentialSum smoothCoefficientAdditiveSum
  apply tsum_congr
  intro n
  rw [additivePhase_add,← unit_nat_phase (-u) n,Units.val_neg,neg_mul,
    ← stdAddChar_conj,unit_nat_phase,additivePhase_conj]
  have he : (n : ℝ)*(-((u : ZMod q).val : ℝ)/q+ξ/X) =
      -(((u : ZMod q).val : ℝ)*n/q)+ξ*n/X := by ring
  rw [he,additivePhase_add]

theorem smoothCoefficientAdditiveSum_add_int (B : ℕ) (X θ : ℝ) (w : ℝ → ℝ) (k : ℤ) :
    smoothCoefficientAdditiveSum B X (θ+k) w = smoothCoefficientAdditiveSum B X θ w := by
  unfold smoothCoefficientAdditiveSum
  apply tsum_congr
  intro n
  have he : (n : ℝ)*(θ+k) = n*θ+((n : ℤ)*k : ℤ) := by push_cast; ring
  rw [he,additivePhase_add_int]

theorem lifted_arc_smooth_coefficient {j q : ℕ} [NeZero j] [NeZero q] [NeZero (j*q)]
    (B : ℕ) (t : Fin j) (r : Fin q) (hr : r.val.Coprime q)
    {X : ℝ} (hX : X ≠ 0) (ξ : ℝ) (w : ℝ → ℝ) :
    smoothCoefficientAdditiveSum B X (-(j : ℝ)*
      (((arcLiftEquiv j q (t,r)).val : ℝ)/(j*q : ℕ)+ξ/((j : ℝ)*X))) w =
      coefficientExponentialSum B q (-(ZMod.unitOfCoprime r.val hr)) (-ξ) X w := by
  have hj : (j : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne j
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [arcLiftEquiv_location,coefficientExponentialSum_neg_unit,ZMod.coe_unitOfCoprime,
    ZMod.val_natCast,Nat.mod_eq_of_lt r.isLt]
  have he : -(j : ℝ)*(((r.val : ℝ)/q+t.val)/j+ξ/((j : ℝ)*X)) =
      (-(r.val : ℝ)/q+(-ξ)/X)+(-(t.val : ℤ) : ℤ) := by
    push_cast
    field_simp
    ring
  rw [he,smoothCoefficientAdditiveSum_add_int]

end JointDickman

end OAI
