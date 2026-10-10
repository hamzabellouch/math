import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexifiedCartan
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexRotationTorus

namespace OAI

/-! # Conjugation of the complex Cartan weight spaces -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- The conjugation induced on the actual complexified Cartan subalgebra. -/
def cartanConjugation (h : complexifiedSubalgebra L H) : complexifiedSubalgebra L H :=
  ⟨complexificationConjugation L h, complexifiedSubalgebra_conjugation L H h.property⟩

omit [H.IsCartanSubalgebra] in
@[simp] theorem cartanConjugation_involutive (h : complexifiedSubalgebra L H) :
    cartanConjugation L H (cartanConjugation L H h) = h := by
  apply Subtype.ext
  exact complexificationConjugation_involutive L h

/-- Complex conjugation sends a weight to its conjugate after conjugating
its Cartan argument. -/
def conjugateCartanWeight (χ : complexifiedSubalgebra L H → ℂ) :
    complexifiedSubalgebra L H → ℂ := fun h => star (χ (cartanConjugation L H h))

omit [H.IsCartanSubalgebra] in
theorem conjugation_ad_sub_pow (χ : complexifiedSubalgebra L H → ℂ)
    (h : complexifiedSubalgebra L H) (k : ℕ) (x : ℂ ⊗[ℝ] L) :
    complexificationConjugation L
      (((toEnd ℂ (complexifiedSubalgebra L H) (ℂ ⊗[ℝ] L) (cartanConjugation L H h) -
        χ (cartanConjugation L H h) • 1) ^ k) x) =
      ((toEnd ℂ (complexifiedSubalgebra L H) (ℂ ⊗[ℝ] L) h -
        conjugateCartanWeight L H χ h • 1) ^ k) (complexificationConjugation L x) := by
  let A := toEnd ℂ (complexifiedSubalgebra L H) (ℂ ⊗[ℝ] L) (cartanConjugation L H h) -
    χ (cartanConjugation L H h) • 1
  let B := toEnd ℂ (complexifiedSubalgebra L H) (ℂ ⊗[ℝ] L) h -
    conjugateCartanWeight L H χ h • 1
  have he (v : ℂ ⊗[ℝ] L) : complexificationConjugation L (A v) =
      B (complexificationConjugation L v) := by
    change complexificationConjugation L
      (⁅(cartanConjugation L H h : ℂ ⊗[ℝ] L), v⁆ - χ (cartanConjugation L H h) • v) =
      ⁅(h : ℂ ⊗[ℝ] L), complexificationConjugation L v⁆ -
        conjugateCartanWeight L H χ h • complexificationConjugation L v
    rw [map_sub, LieEquiv.map_lie, complexificationConjugation_smul]
    change ⁅complexificationConjugation L (complexificationConjugation L h), _⁆ - _ = _
    rw [complexificationConjugation_involutive]
    rfl
  change complexificationConjugation L ((A ^ k) x) = (B ^ k) (complexificationConjugation L x)
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, he, ih]

theorem conjugation_mem_genWeightSpace (χ : complexifiedSubalgebra L H → ℂ)
    {x : ℂ ⊗[ℝ] L} (hx : x ∈ genWeightSpace (ℂ ⊗[ℝ] L) χ) :
    complexificationConjugation L x ∈
      genWeightSpace (ℂ ⊗[ℝ] L) (conjugateCartanWeight L H χ) := by
  apply (mem_genWeightSpace _ _ _).mpr
  intro h
  obtain ⟨k, hk⟩ := (mem_genWeightSpace _ _ _).mp hx (cartanConjugation L H h)
  refine ⟨k, ?_⟩
  rw [← conjugation_ad_sub_pow, hk, map_zero]

end PolycyclicRecognition

end

end OAI
