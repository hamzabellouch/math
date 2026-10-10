import OAI.GroupTheory.PolycyclicRecognition.Algebra.EquivariantLangTransversal
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialInnerUnipotence

namespace OAI

/-! # Inner correction while preserving a previously chosen symmetry family -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem jordan_inner_twist_normal_form_fixed {ι : Type*}
    (A S U : L ≃ₗ⁅ℝ⁆ L) (T : ι → L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (hTS : ∀ i, Commute (T i).toLinearMap S.toLinearMap)
    (hTU : ∀ i, Commute (T i).toLinearMap U.toLinearMap)
    (u : L) (htu : ∀ i, T i u = u) :
    ∃ (v : L) (W : L ≃ₗ⁅ℝ⁆ L), IsNilpotent (W.toLinearMap - 1) ∧
      Commute S.toLinearMap W.toLinearMap ∧ (∀ i, T i v = v) ∧
      (∀ i, Commute (T i).toLinearMap W.toLinearMap) ∧
      ∀ x : L, v * (u * A (v⁻¹ * x * v) * u⁻¹) * v⁻¹ = S (W x) := by
  have hTA (i : ι) : Commute (T i).toLinearMap A.toLinearMap := by
    rw [hA]
    exact (hTS i).mul_right (hTU i)
  obtain ⟨v, w, hSw, hTv, hTw, hu⟩ :=
    jordan_lang_decomposition_fixed_family A S U T hS hU hSU hA hTS hTA u htu
  let W := U.trans (polynomialInnerLieEquiv w)
  have hW (x : L) : W x = w * U x * w⁻¹ := polynomialInnerLieEquiv_apply w (U x)
  have hcomm (R : L ≃ₗ⁅ℝ⁆ L) (hw : R w = w)
      (hRU : Commute R.toLinearMap U.toLinearMap) : Commute R.toLinearMap W.toLinearMap := by
    apply LinearMap.ext
    intro x
    change R (W x) = W (R x)
    rw [hW, hW]
    let r := PolynomialExponentialCoordinates.groupAutomorphism (P := C) R
    change r (w * U x * w⁻¹) = w * U (R x) * w⁻¹
    rw [map_mul, map_mul, map_inv]
    change R w * R (U x) * (R w)⁻¹ = w * U (R x) * w⁻¹
    rw [hw]
    have hh : R (U x) = U (R x) := LinearMap.congr_fun hRU.eq x
    rw [hh]
  refine ⟨v, W, polynomial_inner_mul_unipotent U hU w, hcomm S hSw hSU,
    hTv, fun i => hcomm (T i) (hTw i) (hTU i), ?_⟩
  intro x
  let a := PolynomialExponentialCoordinates.groupAutomorphism (P := C) A
  have hr : v * (u * A (v⁻¹ * x * v) * u⁻¹) * v⁻¹ = w * A x * w⁻¹ := by
    change v * (u * a (v⁻¹ * x * v) * u⁻¹) * v⁻¹ = w * a x * w⁻¹
    change u = v⁻¹ * w * a v at hu
    rw [hu]
    simp only [map_mul, map_inv]
    group
  rw [hr, hW]
  have hAx : A x = S (U x) := LinearMap.congr_fun hA x
  rw [hAx]
  let s := PolynomialExponentialCoordinates.groupAutomorphism (P := C) S
  change w * S (U x) * w⁻¹ = s (w * U x * w⁻¹)
  rw [map_mul, map_mul, map_inv]
  change w * S (U x) * w⁻¹ = S w * S (U x) * (S w)⁻¹
  rw [hSw]

end PolycyclicRecognition

end

end OAI
