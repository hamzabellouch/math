import OAI.Analysis.Mahler.HemisphereChart

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace MahlerStokes

/-- Move the distinguished coordinate first without changing the relative
order of any other coordinates. The same reindexing is used on both matrix axes. -/
def splitCoordinate {n : ℕ} (i : Fin (n+1)) : Fin 1 ⊕ Fin n ≃ Fin (n+1) :=
  Equiv.ofBijective (Sum.elim (fun _ => i) i.succAbove) (by
    constructor
    · intro a b h
      rcases a with a | a <;> rcases b with b | b
      · congr 1; exact Subsingleton.elim _ _
      · exact (i.succAbove_ne b h.symm).elim
      · exact (i.succAbove_ne a h).elim
      · exact congrArg Sum.inr (i.succAbove_right_injective h)
    · rw [Function.Surjective, i.forall_iff_succAbove]
      exact ⟨⟨Sum.inl 0, rfl⟩, fun j => ⟨Sum.inr j, rfl⟩⟩)

def hemisphereFrameMatrix {n : ℕ} (y : Fin n → ℝ) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (fun _ _ => chord 1 y) (fun _ j => -(chord 1 y)⁻¹ * y j)
    (fun j _ => y j) 1

@[simp] lemma splitCoordinate_inl {n : ℕ} (i : Fin (n+1)) (index : Fin 1) :
    splitCoordinate i (Sum.inl index) = i := rfl

@[simp] lemma splitCoordinate_inr {n : ℕ} (i : Fin (n+1)) (index : Fin n) :
    splitCoordinate i (Sum.inr index) = i.succAbove index := rfl

lemma det_hemisphereFrameMatrix {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    (hemisphereFrameMatrix y).det = (chord 1 y)⁻¹ := by
  change (Matrix.fromBlocks (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => chord 1 y))
    (Matrix.of (fun _ j => -(chord 1 y)⁻¹ * y j))
    (Matrix.of (fun j _ => y j)) (1 : Matrix (Fin n) (Fin n) ℝ)).det = _
  rw [Matrix.det_fromBlocks_one₂₂, Matrix.det_fin_one]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply]
  have hs : (∑ j, (-(chord 1 y)⁻¹ * y j) * y j) =
      -(chord 1 y)⁻¹ * radiusSq y := by
    rw [radiusSq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  have hc := chord_sq hy
  have hn := (chord_pos hy).ne'
  field_simp
  nlinarith

lemma hemisphereConeDerivative_matrix {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
    (LinearMap.toMatrix' (hemisphereConeDerivative i x).toLinearMap).submatrix
      (splitCoordinate i) (splitCoordinate i) =
    Matrix.updateCol (x i • hemisphereFrameMatrix (i.removeNth x)) (Sum.inl 0)
      (fun j => hemisphereFrameMatrix (i.removeNth x) j (Sum.inl 0)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  all_goals try (have hb : b = (0 : Fin 1) := Subsingleton.elim _ _; subst b)
  all_goals
    simp [LinearMap.toMatrix'_apply, hemisphereConeDerivative,
      hemisphereGraphDerivative, removeCoordinate, hemisphereGraph, chordDerivative,
      coordinateDot, hemisphereFrameMatrix, Matrix.updateCol, Matrix.fromBlocks,
      Fin.removeNth, Pi.single_apply, Function.update,
      Fin.ne_succAbove, eq_comm, mul_comm, Matrix.one_apply, mul_ite, mul_one, mul_zero]

/-- The actual ambient Jacobian of radial hemisphere coordinates. The
singularity is only at the equator, outside the open parameter domain. -/
theorem det_hemisphereConeDerivative {n : ℕ} (i : Fin (n+1))
    {x : Fin (n+1) → ℝ} (hx : x ∈ hemisphereConeDomain i) :
    (hemisphereConeDerivative i x).toLinearMap.det =
      (x i)^n * (chord 1 (i.removeNth x))⁻¹ := by
  rw [← LinearMap.det_toMatrix', ← Matrix.det_submatrix_equiv_self (splitCoordinate i),
    hemisphereConeDerivative_matrix, Matrix.det_updateCol_smul_left,
    Matrix.updateCol_eq_self, det_hemisphereFrameMatrix hx.2]
  simp

end MahlerStokes

end

end OAI
