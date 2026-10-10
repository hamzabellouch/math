import OAI.Combinatorics.Progressions.Lattices.TriangularAffineReset
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchResidualCell

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped NNReal

namespace PolynomialPatch

theorem exists_uniform_weight_torus_model {σ : Type*} {s d h : ℕ}
    (A : PolynomialPatch σ s d) (hh : 0 < h) (hw : ∀ i, A.weight i = h) :
    ∃ (F : (Fin d → ℝ) → ℝ) (Q : Fin d → MvPolynomial σ ℝ),
      LipschitzWith (A.kernel.lip * d) F ∧
      (∀ x, F x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x : Fin d → ℝ, ∀ m : Fin d → ℤ, F (fun i => x i + m i) = F x) ∧
      (∀ i, Q i ∈ weightedSupportLE (fun _ : σ => 1) h) ∧
      ∀ t : σ → ℝ, A.value t = F (fun i => aeval t (Q i)) := by
  let L := A.lowestLayerModel (D := d) (E := 0) hh (fun i => hw (i.castAdd 0))
  let T := 1 - L.matrix
  have hTtri : T.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    simp only [T, Matrix.sub_apply, Matrix.one_apply_ne hij.ne,
      L.strict i j hij.le, sub_self]
  have hTdiag : ∀ i, T i i = 1 := by
    intro i
    simp [T, Matrix.sub_apply, L.strict i i le_rfl]
  let U := triangularReductionMatrix T
  let V := U⁻¹.map (Int.castRingHom ℝ)
  let B := reducedTriangularMatrix T
  let Q := polynomialMatrixAction V L.origin
  have hU : IsUnit U.det := by rw [triangularReductionMatrix_det]; exact isUnit_one
  refine ⟨triangularLatticeValue B A.kernel, Q,
    triangularLatticeValue_lipschitz B
      (reducedTriangularMatrix_above T hTtri hTdiag)
      (reducedTriangularMatrix_diag T hTtri hTdiag)
      (reducedTriangularMatrix_bound T hTtri hTdiag) A.kernel,
    triangularLatticeValue_mem_Icc B
      (reducedTriangularMatrix_above T hTtri hTdiag)
      (reducedTriangularMatrix_diag T hTtri hTdiag) A.kernel,
    triangularLatticeValue_integer_periodic B A.kernel,
    polynomialMatrixAction_degree V L.origin L.degree, ?_⟩
  intro t
  have hslots := L.form_eq t
  rw [TriangularSlots.takePrefix_zero] at hslots
  have hraw : A.value t = triangularLatticeValue T A.kernel
      (fun i => aeval t (L.origin i)) := by
    change (A.form.slots t).patchValue A.kernel = _
    rw [hslots]
    simp only [TriangularSlots.patchValue, TriangularSlots.affineBlock_residual,
      triangularLatticeValue, T]
  rw [hraw, triangularLatticeValue_change_basis T U hU A.kernel]
  change triangularLatticeValue B A.kernel (V.mulVec (fun i => aeval t (L.origin i))) =
    triangularLatticeValue B A.kernel (fun i => aeval t (polynomialMatrixAction V L.origin i))
  rw [polynomialMatrixAction_eval]

end PolynomialPatch
end Erdos3

end

end OAI
