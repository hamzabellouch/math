import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # Uniqueness of the multiplicative semisimple factor -/

namespace PolycyclicRecognition
variable {K V : Type*} [Field K] [PerfectField K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem multiplicative_jordan_semisimple_unique
    (S₁ U₁ S₂ U₂ : Module.End K V)
    (hS₁ : S₁.IsSemisimple) (hU₁ : IsNilpotent (U₁ - 1))
    (hS₂ : S₂.IsSemisimple) (hU₂ : IsNilpotent (U₂ - 1))
    (hC₁ : Commute S₁ U₁) (hC₂ : Commute S₂ U₂)
    (h : S₁ * U₁ = S₂ * U₂) : S₁ = S₂ := by
  have hc₁ : Commute S₁ (U₁ - 1) := hC₁.sub_right (Commute.one_right S₁)
  have hc₂ : Commute S₂ (U₂ - 1) := hC₂.sub_right (Commute.one_right S₂)
  have hn₁ : IsNilpotent (S₁ * (U₁ - 1)) := hc₁.isNilpotent_mul_left hU₁
  have hn₂ : IsNilpotent (S₂ * (U₂ - 1)) := hc₂.isNilpotent_mul_left hU₂
  apply (Module.End.isNilpotent_isSemisimple_unique hn₁ hS₁ hn₂ hS₂
    ((Commute.refl S₁).mul_left hc₁.symm)
    ((Commute.refl S₂).mul_left hc₂.symm) ?_).2
  simpa only [mul_sub, mul_one, sub_add_cancel] using h

omit [PerfectField K] [FiniteDimensional K V] in
theorem semisimple_conj (e : V ≃ₗ[K] V) (S : Module.End K V) (hS : S.IsSemisimple) :
    (e.conjRingEquiv S).IsSemisimple := by
  apply (e.isSemisimple_iff S (e.conjRingEquiv S) ?_).mp hS
  apply LinearMap.ext
  intro x
  simp

end PolycyclicRecognition

end OAI
