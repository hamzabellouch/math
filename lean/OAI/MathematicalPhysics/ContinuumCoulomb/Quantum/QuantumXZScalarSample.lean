import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumExchangeSample

namespace OAI

/-! The computed scalar correction for the complete private-pair X/Z family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem shiftValue_cast (a : Fin 2) (q : ℚ) :
    (shiftValue a q:ℝ) = qmaFourAxisFieldShift a (q:ℝ) := by
  unfold shiftValue qmaFourAxisFieldShift
  split_ifs <;> norm_num

def scalarValue (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) : ℚ :=
  r^2*(n*6)+(∑ e : QMAXZScalarIndex t, J e.val)-
    (∑ e : QMAXZPairIndex t, offset k (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val))-
    ∑ e : QMAXZFieldIndex t, shiftValue (qmaXZFieldData t e).axis (J e.val)

theorem scalarValue_sub (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    (scalarValue k r t J:ℝ)-qmaFourExchangeScalar n (r:ℝ)
      (fun e => (qmaXZFieldData t e).axis) (fun e => (J e.val:ℝ))
      (qmaXZFamilyConstant t (fun e => (J e:ℝ))) =
    ∑ e : QMAXZPairIndex t,
      (qmaFourEnergyOffset (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val:ℝ)-
        (offset k (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val):ℝ)) := by
  simp only [scalarValue,qmaFourExchangeScalar,qmaXZFamilyConstant,qmaFourTensorFieldShift,
    Rat.cast_sub,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,
    Rat.cast_sum,shiftValue_cast,Finset.sum_sub_distrib]
  ring

theorem scalarValue_error (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    |(scalarValue k r t J:ℝ)-qmaFourExchangeScalar n (r:ℝ)
      (fun e => (qmaXZFieldData t e).axis) (fun e => (J e.val:ℝ))
      (qmaXZFamilyConstant t (fun e => (J e:ℝ)))| ≤
        (320800*(∑ e, |(J e:ℝ)|))*(2:ℝ)⁻¹^k := by
  rw [scalarValue_sub]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ e : QMAXZPairIndex t, 320800*|(J e.val:ℝ)| *(2:ℝ)⁻¹^k := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_sub_comm]
      exact offset_error k _ _ _
    _ = (320800*(∑ e : QMAXZPairIndex t, |(J e.val:ℝ)|))*(2:ℝ)⁻¹^k := by
      rw [Finset.mul_sum,Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (qmaSum_subtype_abs_le (fun e => (t e).IsPair) (fun e => (J e:ℝ)))
        (by norm_num)) (by positivity)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
