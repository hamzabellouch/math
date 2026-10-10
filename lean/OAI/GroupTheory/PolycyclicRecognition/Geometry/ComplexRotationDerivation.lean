import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexRotationTorus
import Mathlib.Algebra.Lie.Derivation.Basic

namespace OAI

/-! # The infinitesimal imaginary Cartan action

The infinitesimal compact action is a genuine Lie derivation. Subtracting
it from the original adjoint action removes exactly the imaginary weights.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan
open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

/-- Imaginary semisimple part of a Cartan adjoint operator. -/
def imaginaryOperator (h : H) : L →ₗ[ℂ] L :=
  weightOperator H (fun χ => imaginaryPart (χ h))

theorem imaginaryOperator_apply (h : H) (χ : Weight ℂ H L)
    {x : L} (hx : x ∈ genWeightSpace L χ) :
    imaginaryOperator H h x = imaginaryPart (χ h) • x :=
  weightOperator_apply H _ χ hx

theorem imaginaryOperator_apply_genWeight (h : H) (χ : H → ℂ)
    {x : L} (hx : x ∈ genWeightSpace L χ) :
    imaginaryOperator H h x = imaginaryPart (χ h) • x := by
  by_cases hχ : genWeightSpace L χ = ⊥
  · have hx0 : x = 0 := by simpa only [hχ,LieSubmodule.mem_bot] using hx
    simp [hx0]
  · exact imaginaryOperator_apply H h ⟨χ,hχ⟩ hx

/-- The root-bracket rule makes the imaginary semisimple part a derivation. -/
theorem imaginaryOperator_lie (h : H) (x y : L) :
    imaginaryOperator H h ⁅x,y⁆ =
      ⁅imaginaryOperator H h x,y⁆ + ⁅x,imaginaryOperator H h y⁆ := by
  apply root_induction H (x := x)
  · intro χ u hu
    apply root_induction H (x := y)
    · intro ψ v hv
      rw [imaginaryOperator_apply_genWeight H h (χ + ψ)
        (lie_mem_genWeightSpace_of_mem_genWeightSpace hu hv),
        imaginaryOperator_apply H h χ hu,imaginaryOperator_apply H h ψ hv]
      simp only [Pi.add_apply,map_add,add_smul,smul_lie,lie_smul]
    · simp
    · intro v w hv hw
      simp only [lie_add,map_add,hv,hw]
      abel
  · simp
  · intro u v hu hv
    simp only [add_lie,map_add,hu,hv]
    abel

/-- The infinitesimal rotation as a bundled derivation. -/
def imaginaryDerivation (h : H) : LieDerivation ℂ L L where
  toLinearMap := imaginaryOperator H h
  leibniz' x y := by
    rw [imaginaryOperator_lie,← lie_skew (imaginaryOperator H h x) y]
    simp only [sub_eq_add_neg,add_comm]

@[simp] theorem imaginaryOperator_add (h k : H) (x : L) :
    imaginaryOperator H (h+k) x = imaginaryOperator H h x + imaginaryOperator H k x := by
  apply root_induction H (x := x)
  · intro χ v hv
    simp only [imaginaryOperator_apply H _ χ hv,map_add,add_smul]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw]
    abel

@[simp] theorem imaginaryOperator_zero (x : L) : imaginaryOperator H 0 x = 0 := by
  apply root_induction H (x := x)
  · intro χ v hv
    simp only [imaginaryOperator_apply H _ χ hv,map_zero,zero_smul]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw,add_zero]

/-- Dependence on the Cartan parameter is real linear. -/
theorem imaginaryOperator_real_smul (r : ℝ) (h : H) (x : L) :
    imaginaryOperator H (r • h) x = r • imaginaryOperator H h x := by
  apply root_induction H (x := x)
  · intro χ v hv
    rw [imaginaryOperator_apply H _ χ hv,imaginaryOperator_apply H _ χ hv,
      LinearMapClass.map_smul_of_tower, map_smul, smul_assoc]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw,smul_add]

/-- The imaginary operators commute, including on generalized weight spaces. -/
theorem imaginaryOperator_commute (h k : H) (x : L) :
    imaginaryOperator H h (imaginaryOperator H k x) =
      imaginaryOperator H k (imaginaryOperator H h x) := by
  apply root_induction H (x := x)
  · intro χ v hv
    rw [imaginaryOperator_apply H k χ hv,imaginaryOperator_apply H h χ hv,
      map_smul,map_smul,imaginaryOperator_apply H h χ hv,
      imaginaryOperator_apply H k χ hv,smul_smul,smul_smul,mul_comm]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw]

/-- The zero-weight Cartan algebra is fixed infinitesimally. -/
theorem imaginaryOperator_cartan (h k : H) : imaginaryOperator H h k = 0 := by
  have hk : (k : L) ∈ genWeightSpace L (0 : H → ℂ) := by
    change (k : L) ∈ rootSpace H 0
    rw [rootSpace_zero_eq]
    exact k.property
  rw [imaginaryOperator_apply_genWeight H h 0 hk]
  simp

end PolycyclicRecognition.ComplexCartan

end

end OAI
