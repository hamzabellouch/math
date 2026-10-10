import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexRotationDerivation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! # The derivative of a Cartan phase along a real line -/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan
open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

local instance : NormedAddCommGroup L := rotationNormedAddCommGroup
local instance : NormedSpace ℂ L := rotationNormedSpace
local instance : NormedSpace ℝ L := NormedSpace.restrictScalars ℝ ℂ L

theorem hasDerivAt_phase_line (h : H) (χ : Weight ℂ H L) :
    HasDerivAt (fun t : ℝ => phase H (t • h) χ) (imaginaryPart (χ h)) 0 := by
  have hd := ((hasDerivAt_id (0 : ℝ)).smul_const (imaginaryPart (χ h))).cexp
  have he (t : ℝ) : χ (t • h) = t • χ h :=
    (χ : H →ₗ[ℂ] ℂ).map_smul_of_tower t h
  simpa only [phase,he,map_smul,id_eq,zero_smul,
    Complex.exp_zero,one_smul,mul_one,one_mul] using hd

theorem hasDerivAt_rotation_line (h : H) (x : L) :
    HasDerivAt (fun t : ℝ => rotationLinear H (t • h) x) (imaginaryOperator H h x) 0 := by
  apply root_induction H (x := x)
  · intro χ v hv
    have hd := (hasDerivAt_phase_line H h χ).smul_const v
    simpa only [rotationLinear_apply H _ χ hv,imaginaryOperator_apply H h χ hv] using hd
  · simpa only [map_zero] using (hasDerivAt_const (0 : ℝ) (0 : L))
  · intro v w hv hw
    rw [map_add]
    exact (hv.add hw).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun t => map_add (rotationLinear H (t • h)) v w))

end PolycyclicRecognition.ComplexCartan

end

end OAI
