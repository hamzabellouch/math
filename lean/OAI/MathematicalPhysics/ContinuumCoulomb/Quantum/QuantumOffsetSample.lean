import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCountertermProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFieldSample

namespace OAI

/-! Error bounds for the sampled counterterm fields and their scalar shifts. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

theorem counterA_abs (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(counterA k a b t:ℝ)| ≤ 400*|(t:ℝ)| := by
  simp only [counterA,Rat.cast_mul,Rat.cast_abs,shift_cast,sign_cast,abs_mul,abs_abs,
    abs_of_nonneg (value_bounds k b).1]
  calc
    _ ≤ (|(t:ℝ)| *1)*400 := mul_le_mul
      (mul_le_mul_of_nonneg_left (value_bounds k b).2 (abs_nonneg _))
      (qmaFourAxisShift_abs_bound b _) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem counterB_abs (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(counterB k a b t:ℝ)| ≤ 400*|(t:ℝ)| := by
  simp only [counterB,Rat.cast_mul,Rat.cast_abs,shift_cast,polarity_cast,abs_mul,abs_abs,
    abs_of_nonneg (value_bounds k a).1,qmaFourAxisSign_abs,mul_one]
  calc
    _ ≤ (|(t:ℝ)| *1)*400 := mul_le_mul
      (mul_le_mul_of_nonneg_left (value_bounds k a).2 (abs_nonneg _))
      (qmaFourAxisShift_abs_bound a true) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem counterFieldA_error (k : ℕ) (a b : Fin 2) (t : ℚ) (e : Fin 3) :
    |(fieldValue k a (counterA k a b t) e:ℝ)-qmaFieldEdgeWeight a (qmaFourCounterA a b (t:ℝ)) e| ≤
      26000*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  have hfield := fieldValue_error k a (counterA k a b t) e
  have hcoef := counterA_abs k a b t
  have hsample := counterA_error k a b t
  have hweight := (fieldWeight_lipschitz a (counterA k a b t:ℝ) (qmaFourCounterA a b (t:ℝ)) e).trans hsample
  apply ((abs_sub_le _ _ _).trans (add_le_add hfield hweight)).trans
  have hm := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (2:ℝ)⁻¹^k)
  nlinarith

theorem counterFieldB_error (k : ℕ) (a b : Fin 2) (t : ℚ) (e : Fin 3) :
    |(fieldValue k b (counterB k a b t) e:ℝ)-qmaFieldEdgeWeight b (qmaFourCounterB a b (t:ℝ)) e| ≤
      26000*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  have hfield := fieldValue_error k b (counterB k a b t) e
  have hcoef := counterB_abs k a b t
  have hsample := counterB_error k a b t
  have hweight := (fieldWeight_lipschitz b (counterB k a b t:ℝ) (qmaFourCounterB a b (t:ℝ)) e).trans hsample
  apply ((abs_sub_le _ _ _).trans (add_le_add hfield hweight)).trans
  have hm := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (2:ℝ)⁻¹^k)
  nlinarith

def shiftValue (a : Fin 2) (t : ℚ) : ℚ := if a = 0 then 0 else t/2

theorem shiftValue_error (a : Fin 2) (q : ℚ) (x : ℝ) :
    |(shiftValue a q:ℝ)-qmaFourAxisFieldShift a x| ≤ |(q:ℝ)-x| := by
  by_cases ha : a = 0
  · simp [shiftValue,qmaFourAxisFieldShift,ha]
  · simp only [shiftValue,qmaFourAxisFieldShift,ha,ite_false,Rat.cast_div,Rat.cast_ofNat]
    rw [← sub_div,abs_div]
    norm_num

def offset (k : ℕ) (a b : Fin 2) (t : ℚ) : ℚ :=
  shiftValue a (counterA k a b t)+shiftValue b (counterB k a b t)-
    factor k a b t*shift a true*shift b (decide (t ≤ 0))

theorem offset_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(offset k a b t:ℝ)-qmaFourEnergyOffset a b (t:ℝ)| ≤
      320800*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  have ha := (shiftValue_error a (counterA k a b t) (qmaFourCounterA a b (t:ℝ))).trans
    (counterA_error k a b t)
  have hb := (shiftValue_error b (counterB k a b t) (qmaFourCounterB a b (t:ℝ))).trans
    (counterB_error k a b t)
  have hc : |((factor k a b t:ℝ)-qmaFourCouplingFactor a b (t:ℝ))*qmaFourAxisShift a true*
      qmaFourAxisShift b (qmaFourCouplingSign (t:ℝ))| ≤ 320000*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ ((2*|(t:ℝ)| *(2:ℝ)⁻¹^k)*400)*400 := mul_le_mul
        (mul_le_mul (factor_error k a b t) (qmaFourAxisShift_abs_bound a true)
          (abs_nonneg _) (by positivity)) (qmaFourAxisShift_abs_bound b _)
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have he : (offset k a b t:ℝ)-qmaFourEnergyOffset a b (t:ℝ) =
      ((shiftValue a (counterA k a b t):ℝ)-qmaFourAxisFieldShift a (qmaFourCounterA a b (t:ℝ)))+
      ((shiftValue b (counterB k a b t):ℝ)-qmaFourAxisFieldShift b (qmaFourCounterB a b (t:ℝ)))-
      ((factor k a b t:ℝ)-qmaFourCouplingFactor a b (t:ℝ))*qmaFourAxisShift a true*
        qmaFourAxisShift b (qmaFourCouplingSign (t:ℝ)) := by
    simp only [offset,qmaFourEnergyOffset,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,shift_cast,sign_cast]
    ring
  rw [he]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_add_le _ _) le_rfl).trans
  calc
    _ ≤ (400*|(t:ℝ)| *(2:ℝ)⁻¹^k+400*|(t:ℝ)| *(2:ℝ)⁻¹^k)+320000*|(t:ℝ)| *(2:ℝ)⁻¹^k :=
      add_le_add (add_le_add ha hb) hc
    _ = _ := by ring

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
