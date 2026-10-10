import OAI.Analysis.MarkovType.OrderedNorm
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def CoordinateSpace (_N : OrderedNorm) (m : ℕ) := Fin m → ℝ

namespace CoordinateSpace

variable (N : OrderedNorm) (m : ℕ)

instance : AddCommGroup (CoordinateSpace N m) :=
  inferInstanceAs (AddCommGroup (Fin m → ℝ))

instance : Module ℝ (CoordinateSpace N m) :=
  inferInstanceAs (Module ℝ (Fin m → ℝ))

instance : FiniteDimensional ℝ (CoordinateSpace N m) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin m → ℝ))

instance : Norm (CoordinateSpace N m) := ⟨fun a => N (C00.ofArray a)⟩

private theorem normCore : NormedSpace.Core ℝ (CoordinateSpace N m) where
  norm_nonneg a := N.nonneg (C00.ofArray a)
  norm_smul r a := by
    change Fin m → ℝ at a
    change N (C00.arrayLinear m (r • a)) = ‖r‖ * N (C00.arrayLinear m a)
    rw [map_smul, N.smul, Real.norm_eq_abs]
  norm_triangle a b := by
    change Fin m → ℝ at a b
    change N (C00.arrayLinear m (a + b)) ≤
      N (C00.arrayLinear m a) + N (C00.arrayLinear m b)
    rw [map_add]
    exact N.add_le _ _
  norm_eq_zero_iff a := by
    change N (C00.ofArray a) = 0 ↔ a = 0
    rw [N.eq_zero_iff]
    constructor
    · intro h
      apply C00.ofArray_injective m
      exact h.trans ((C00.arrayLinear m).map_zero).symm
    · rintro rfl
      exact (C00.arrayLinear m).map_zero

instance : NormedAddCommGroup (CoordinateSpace N m) :=
  NormedAddCommGroup.ofCore (normCore N m)

instance : NormedSpace ℝ (CoordinateSpace N m) :=
  NormedSpace.ofCore (normCore N m)

def coefficients : CoordinateSpace N m ≃ₗ[ℝ] (Fin m → ℝ) :=
  LinearEquiv.refl ℝ _

@[simp] theorem norm_eq (a : CoordinateSpace N m) :
    ‖a‖ = N (C00.ofArray a) := rfl

end CoordinateSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem coordinatesRepresentable_iff (N : OrderedNorm) :
    CoordinatesRepresentable X N ↔
      ∀ (m : ℕ) (ε : ℝ), 0 < ε →
        ∃ T : CoordinateSpace N m →ₗ[ℝ] X, ∀ a,
          ‖a‖ ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + ε) * ‖a‖ := by
  constructor
  · intro h m ε hε
    obtain ⟨T, hT⟩ := h m ε hε
    refine ⟨T.comp (CoordinateSpace.coefficients N m).toLinearMap, ?_⟩
    intro a
    exact hT a
  · intro h m ε hε
    obtain ⟨T, hT⟩ := h m ε hε
    refine ⟨T.comp (CoordinateSpace.coefficients N m).symm.toLinearMap, ?_⟩
    intro a
    exact hT a

end MarkovSuperreflexivity

end

end OAI
