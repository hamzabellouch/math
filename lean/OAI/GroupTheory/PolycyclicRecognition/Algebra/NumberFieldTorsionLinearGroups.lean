import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalTorsionLinearGroups
import Mathlib.LinearAlgebra.Dimension.Finite

namespace OAI

/-! # Torsion linear groups over number fields

Restriction of scalars gives a faithful finite-dimensional rational action.
This statement needs no finite-generation hypothesis on the group.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

theorem finite_of_faithful_numberField_torsion
    {K G : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    [Group G] {n : ℕ} (ι : G →* PolynomialMatrixGroup K n)
    (hι : Function.Injective ι)
    (hpow : ∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1) : Finite G := by
  let ρ : G →* ((Fin n → K) ≃ₗ[ℚ] (Fin n → K)) := {
    toFun g := (linearAction (ι g)).restrictScalars ℚ
    map_one' := by
      apply LinearEquiv.ext
      intro x
      change linearAction (ι 1) x = x
      rw [map_one, map_one]
      rfl
    map_mul' g h := by
      apply LinearEquiv.ext
      intro x
      change linearAction (ι (g * h)) x = linearAction (ι g) (linearAction (ι h) x)
      rw [map_mul, map_mul]
      rfl }
  have hρ : Function.Injective ρ := by
    intro g h he
    apply hι
    apply linearAction.injective
    exact (LinearEquiv.restrictScalars_injective ℚ) he
  let e := (Module.finBasis ℚ (Fin n → K)).equivFun
  let j := coordinateLinearAction ρ e
  apply finite_of_faithful_rational_torsion j _ hpow
  intro g h he
  exact hρ (coordinateLinearAction_eq_implies_eq ρ e he)

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
