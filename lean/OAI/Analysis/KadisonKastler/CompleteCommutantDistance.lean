import OAI.Analysis.KadisonKastler.AmplifiedCommutatorClosure
import OAI.Analysis.KadisonKastler.FiniteOrbitDistance
import OAI.Analysis.FactorGeneration.MatrixSequence

namespace OAI

/-! # The complete commutator-distance formula

The reflection in each simultaneous commutant orbit has norm at most one.
Its commutator is twice the missing orbit component. Finite coefficient
duality and weak operator separation therefore give the sharp factor one half.
-/

namespace KadisonKastler

open Generator
open scoped InnerProductSpace

noncomputable section

theorem projection_reflection_norm_le_one {B : Type*} [CStarAlgebra B]
    (P : B) (hP : IsStarProjection P) : ‖1 - P - P‖ ≤ 1 := by
  let U := 1 - P - P
  have hs : star U = U := by simp only [U, star_sub, star_one, hP.isSelfAdjoint.star_eq]
  have hp : P * P = P := hP.isIdempotentElem.eq
  have hu : star U * U = 1 := by
    rw [hs]
    simp only [U, sub_mul, mul_sub, one_mul, mul_one, hp]
    abel
  have hn : ‖U‖ * ‖U‖ = ‖(1 : B)‖ := by rw [← CStarRing.norm_star_mul_self, hu]
  have ho : ‖(1 : B)‖ * ‖(1 : B)‖ = ‖(1 : B)‖ := by
    rw [← CStarRing.norm_star_mul_self]
    simp
  have hone : ‖(1 : B)‖ ≤ 1 := by nlinarith [norm_nonneg (1 : B)]
  nlinarith [norm_nonneg U]

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem complete_commutator_orbit_bound
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hcb : CompletelyBoundedBy ((innerDerivation T).comp π.toAlgHom.toLinearMap) e)
    (n : ℕ) (x : FiniteHilbert (Fin n) H) :
    ‖diagonalOperator T x -
        (tupleOrbitClosure (generatedVonNeumannAlgebra π.range).commutant.toStarSubalgebra x).starProjection
          (diagonalOperator T x)‖ ≤ (e / 2) * ‖x‖ := by
  let M := generatedVonNeumannAlgebra π.range
  let V := tupleOrbitClosure M.commutant.toStarSubalgebra x
  let P : FiniteHilbert (Fin n) H →L[ℂ] FiniteHilbert (Fin n) H := V.starProjection
  let U : FiniteHilbert (Fin n) H →L[ℂ] FiniteHilbert (Fin n) H := 1 - P - P
  have hP : IsStarProjection P := isStarProjection_starProjection
  have hPm : P ∈ matrixVonNeumann M := by
    apply (mem_matrixVonNeumann_iff_diagonal M P).mpr
    intro a
    exact tupleOrbitProjection_commutes M.commutant.toStarSubalgebra x a
  have hUm : U ∈ matrixVonNeumann M :=
    (matrixVonNeumann M).sub_mem ((matrixVonNeumann M).sub_mem
      (matrixVonNeumann M).one_mem hPm) hPm
  have hUn : ‖U‖ ≤ 1 := projection_reflection_norm_le_one P hP
  have hb := completelyBounded_commutator_generated π T he hcb n U hUm hUn
  let C : FiniteHilbert (Fin n) H →L[ℂ] FiniteHilbert (Fin n) H :=
    diagonalOperator T * U - U * diagonalOperator T
  change ‖C‖ ≤ e at hb
  have hx : P x = x :=
    V.starProjection_eq_self_iff.mpr (mem_tupleOrbitClosure M.commutant.toStarSubalgebra x)
  have heq : C x =
      (-2 : ℂ) • (diagonalOperator T x - P (diagonalOperator T x)) := by
    simp only [C, U, sub_apply, one_apply_eq_self, mul_apply_eq_comp, hx,
      sub_self, zero_sub, map_neg]
    module
  have hn := (C.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg x))
  rw [heq, norm_smul] at hn
  norm_num at hn
  change ‖diagonalOperator T x - P (diagonalOperator T x)‖ ≤ _
  linarith

/-- The sharp strict commutant approximation, for a possibly nonfaithful
star representation of a unital C-star algebra on any Hilbert space. -/
theorem exists_commutant_of_completelyBounded
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hcb : CompletelyBoundedBy ((innerDerivation T).comp π.toAlgHom.toLinearMap) e)
    {r : ℝ} (hr : e / 2 < r) :
    ∃ D : H →L[ℂ] H, (∀ a, D * π a = π a * D) ∧ ‖D - T‖ < r := by
  let M := generatedVonNeumannAlgebra π.range
  obtain ⟨D, hD, hn⟩ := exists_near_algebra_of_finite_orbit_bound
    M.commutant.toStarSubalgebra (Generator.Tracial.vonNeumann_wotClosed M.commutant)
    T (div_nonneg he (by norm_num)) (complete_commutator_orbit_bound π T he hcb) hr
  refine ⟨D, ?_, hn⟩
  intro a
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hD (π a)
    (subset_generatedVonNeumannAlgebra π.range ⟨a, rfl⟩)).symm

end

end KadisonKastler

end OAI
