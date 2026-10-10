import OAI.Analysis.Pureness.Traces.TracialStates
import OAI.Analysis.Pureness.States.NormalizedPositiveState
import Mathlib.Tactic.LinearCombination

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A]

def selfCommutator (a : A) : selfAdjoint A :=
  ⟨star a * a - a * star a, (IsSelfAdjoint.star_mul_self a).sub
    (IsSelfAdjoint.mul_star_self a)⟩

def selfCommutatorSpace : Submodule ℝ (selfAdjoint A) :=
  Submodule.span ℝ (Set.range (selfCommutator (A := A)))

lemma selfCommutator_mem (a : A) : selfCommutator a ∈ selfCommutatorSpace :=
  Submodule.subset_span ⟨a, rfl⟩

theorem linearMap_tracial_of_star_mul (f : A →ₗ[ℂ] ℂ)
    (h : ∀ a : A, f (star a * a) = f (a * star a)) :
    ∀ a b : A, f (a * b) = f (b * a) := by
  intro a b
  have h₁ := h (star a + b)
  have h₂ := h (star a + Complex.I • b)
  simp only [star_add, star_star, add_mul, mul_add, map_add] at h₁
  simp only [star_add, star_star, star_smul, Complex.star_def,
    Complex.conj_I, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    map_add, map_smul] at h₂
  simp only [smul_eq_mul] at h₂
  have ha := h (star a)
  have hb := h b
  simp only [star_star] at ha
  linear_combination (norm := ring_nf)
    (h₁ - ha - hb - Complex.I * (h₂ - ha - hb)) / 2
  simp [Complex.I_sq]

variable [PartialOrder A] [StarOrderedRing A]

def tracialStateOfReal (f : selfAdjoint A →ₗ[ℝ] ℝ)
    (hpos : ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ f a)
    (h1 : f 1 = 1) (hcomm : ∀ a : A, f (selfCommutator a) = 0) :
    TracialState A where
  functional := PositiveLinearMap.mk₀ (selfAdjointFunctionalComplex f) (by
    intro a ha
    change 0 ≤ selfAdjointFunctionalComplex f (⟨a, .of_nonneg ha⟩ : selfAdjoint A)
    rw [selfAdjointFunctionalComplex_apply]
    exact_mod_cast hpos ⟨a, .of_nonneg ha⟩ ha)
  normalized := by
    change selfAdjointFunctionalComplex f ((1 : selfAdjoint A) : A) = 1
    rw [selfAdjointFunctionalComplex_apply, h1, Complex.ofReal_one]
  tracial := linearMap_tracial_of_star_mul (selfAdjointFunctionalComplex f) (by
    intro a
    apply sub_eq_zero.mp
    rw [← map_sub]
    change selfAdjointFunctionalComplex f (selfCommutator a) = 0
    rw [selfAdjointFunctionalComplex_apply, hcomm, Complex.ofReal_zero])
end CuntzPureness

end

end OAI
