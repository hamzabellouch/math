import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAxisSampleProgram

namespace OAI

/-! Certified rational evaluation of each internal physical field coefficient. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram
open Matrix

def fieldX (k : ℕ) (t : ℚ) : ℚ := 64*t*value k 0

def fieldValue (k : ℕ) (a : Fin 2) (t : ℚ) (e : Fin 3) : ℚ :=
  if a = 0 then ![fieldX k t,-fieldX k t,0] e else ![0,0,-t/2] e

theorem inverseScale_field : 64*inverseScale 0 = 1/(2*Real.sqrt 3) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  norm_num only [inverseScale,ite_true]
  field_simp
  nlinarith

theorem fieldX_error (k : ℕ) (t : ℚ) :
    |(fieldX k t:ℝ)-(t:ℝ)/(2*Real.sqrt 3)| ≤ 64*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  have he : (t:ℝ)/(2*Real.sqrt 3) = 64*(t:ℝ)*inverseScale 0 := by
    rw [mul_comm 64 (t:ℝ),mul_assoc,inverseScale_field]
    ring
  rw [he]
  simp only [fieldX,Rat.cast_mul,Rat.cast_ofNat]
  calc
    _ = 64*|(t:ℝ)| *|(value k 0:ℝ)-inverseScale 0| := by
      rw [show 64*(t:ℝ)*(value k 0:ℝ)-64*(t:ℝ)*inverseScale 0 =
        (64*(t:ℝ))*((value k 0:ℝ)-inverseScale 0) by ring,abs_mul,abs_mul]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (value_error k 0) (by positivity)

theorem fieldValue_error (k : ℕ) (a : Fin 2) (t : ℚ) (e : Fin 3) :
    |(fieldValue k a t e:ℝ)-qmaFieldEdgeWeight a (t:ℝ) e| ≤ 64*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  by_cases ha : a = 0
  · fin_cases e
    · simpa [fieldValue,qmaFieldEdgeWeight,ha] using fieldX_error k t
    · simpa [fieldValue,qmaFieldEdgeWeight,ha,neg_div,neg_add_eq_sub,abs_sub_comm] using fieldX_error k t
    · simp [fieldValue,qmaFieldEdgeWeight,ha]
  · fin_cases e <;> simp [fieldValue,qmaFieldEdgeWeight,ha,Rat.cast_div]

theorem fieldWeight_lipschitz (a : Fin 2) (x y : ℝ) (e : Fin 3) :
    |qmaFieldEdgeWeight a x e-qmaFieldEdgeWeight a y e| ≤ |x-y| := by
  have he : qmaFieldEdgeWeight a (x-y) e = qmaFieldEdgeWeight a x e-qmaFieldEdgeWeight a y e := by
    fin_cases a <;> fin_cases e <;> norm_num [qmaFieldEdgeWeight] <;> ring
  rw [← he]
  exact qmaFieldEdgeWeight_bound a (x-y) e

noncomputable opaque fieldXProgram : Procedure radialCode ratCode (fun x => fieldX x.1 x.2) := by
  let scalar := Procedure.ratMul.comp ((Procedure.constant radialCode ratCode 64).pair inputCoefficientProgram)
  let v := (valueProgram 0).comp inputPrecisionProgram
  exact (Procedure.ratMul.comp (scalar.pair v)).congrFun (by intro x; rfl)

noncomputable opaque fieldValueProgram (a : Fin 2) (e : Fin 3) : Procedure radialCode ratCode
    (fun x => fieldValue x.1 a x.2 e) := by
  by_cases ha : a = 0
  · by_cases he0 : e = 0
    · subst e
      exact fieldXProgram.congrFun (by intro x; simp [fieldValue,ha])
    · by_cases he1 : e = 1
      · subst e
        exact (Procedure.ratNeg.comp fieldXProgram).congrFun (by intro x; simp [fieldValue,ha])
      · have he2 : e = 2 := by omega
        subst e
        exact (Procedure.constant radialCode ratCode 0).congrFun (by intro x; simp [fieldValue,ha])
  · by_cases he2 : e = 2
    · subst e
      exact (Procedure.ratMul.comp (inputCoefficientProgram.pair
        (Procedure.constant radialCode ratCode (-1/2)))).congrFun (by
          intro x
          simp [fieldValue,ha,Function.comp_apply]
          ring)
    · by_cases he0 : e = 0
      · subst e
        exact (Procedure.constant radialCode ratCode 0).congrFun (by intro x; simp [fieldValue,ha])
      · have he1 : e = 1 := by omega
        subst e
        exact (Procedure.constant radialCode ratCode 0).congrFun (by intro x; simp [fieldValue,ha])

noncomputable def fieldValueCertificate (a : Fin 2) (e : Fin 3) : Turing.TM2ComputableInPolyTime
    radialCode ratCode (fun x => fieldValue x.1 a x.2 e) := (fieldValueProgram a e).toTM2

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
