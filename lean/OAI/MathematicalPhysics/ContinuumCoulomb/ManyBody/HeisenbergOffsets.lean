import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.SuperexchangeSpectrum

namespace OAI

/-! Exact scalar offsets and positive homogeneity connecting the ordinary
finite-spin Hamiltonian with the Hubbard superexchange source form. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace

variable {Edge : Type*} [Fintype Edge]

def finiteHeisenbergMatrix (n : ℕ) (left right : Edge → Fin n) (J : Edge → ℝ) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e)

def finiteHeisenbergBottom (n : ℕ) (left right : Edge → Fin n) (J : Edge → ℝ) : ℝ :=
  sourceMatrixBottom n (finiteHeisenbergMatrix n left right J)

theorem sourceMatrixForm_smul (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (a : ℝ)
    (p : MediatorLowSpace n) :
    ⟪p, spinMatrixOperator ((a : ℂ) • M) p⟫_ℝ = a * ⟪p, spinMatrixOperator M p⟫_ℝ := by
  rw [spinMatrixOperator_smul, _root_.smul_apply,
    HubbardGlobal.euclidean_real_inner, inner_smul_right, HubbardGlobal.euclidean_real_inner]
  change ((a : ℂ) * ⟪p, spinMatrixOperator M p⟫_ℂ).re =
    a * (⟪p, spinMatrixOperator M p⟫_ℂ).re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem sourceMatrixBottom_smul (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) {a : ℝ} (ha : 0 ≤ a) :
    sourceMatrixBottom n ((a : ℂ) • M) = a * sourceMatrixBottom n M := by
  obtain ⟨p, hp, hb, hmin⟩ := sourceMatrixBottom_minimizer n M
  obtain ⟨q, hq, hbq, hminq⟩ := sourceMatrixBottom_minimizer n ((a : ℂ) • M)
  rw [hb, hbq, sourceMatrixForm_smul]
  apply le_antisymm
  · have h := hminq p hp
    rw [sourceMatrixForm_smul, sourceMatrixForm_smul] at h
    exact h
  · exact mul_le_mul_of_nonneg_left (hmin q hq) ha

theorem finiteHeisenbergBottom_smul (n : ℕ) (left right : Edge → Fin n) (J : Edge → ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    finiteHeisenbergBottom n left right (fun e => a * J e) =
      a * finiteHeisenbergBottom n left right J := by
  have hmat : finiteHeisenbergMatrix n left right (fun e => a * J e) =
      (a : ℂ) • finiteHeisenbergMatrix n left right J := by
    simp only [finiteHeisenbergMatrix, Finset.smul_sum, Complex.ofReal_mul, smul_smul]
  rw [finiteHeisenbergBottom, hmat, sourceMatrixBottom_smul n _ ha]
  rfl

theorem finiteHeisenbergBottom_bonds {n r : ℕ} (F : MediatorIteration.Bonds n r) :
    finiteHeisenbergBottom n F.left F.right (fun e => (F.weight e : ℝ)) =
      sourceMatrixBottom n F.matrix := rfl

namespace HubbardGlobal

theorem graphSourceAction_matrix (m : ℕ) (left right : Edge → Fin (m + 1))
    (J : Edge → ℝ) (u : SourceSpinVector (m + 1)) :
    (finiteHeisenbergMatrix (m + 1) left right J - ((∑ e, J e : ℝ) : ℂ) • 1) *ᵥ u =
      graphSourceAction m left right (fun e => (J e : ℂ)) u := by
  rw [Matrix.sub_mulVec]
  simp only [finiteHeisenbergMatrix, Matrix.sum_mulVec, Matrix.smul_mulVec,
    sourceHeisenbergMatrix_mulVec, Matrix.one_mulVec]
  ext s
  simp only [graphSourceAction, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, mul_sub, Complex.ofReal_sum, Finset.sum_mul]

theorem graphSourceForm_matrix (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℝ)
    (p : MediatorLowSpace (m + 1)) :
    graphSourceForm m left right J (fun s => p s) =
      ⟪p, spinMatrixOperator
        (finiteHeisenbergMatrix (m + 1) left right J - ((∑ e, J e : ℝ) : ℂ) • 1) p⟫_ℝ := by
  rw [graphSourceForm_expectation, euclidean_real_inner]
  have hact : spinMatrixOperator
      (finiteHeisenbergMatrix (m + 1) left right J - ((∑ e, J e : ℝ) : ℂ) • 1) p =
        WithLp.toLp 2 (graphSourceAction m left right (fun e => (J e : ℂ)) (fun s => p s)) := by
    ext s
    exact congrFun (graphSourceAction_matrix m left right J (fun s => p s)) s
  rw [hact, PiLp.inner_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  simp only [RCLike.inner_apply]
  exact mul_comm _ _

/-- Hubbard's `Heisenberg - I` convention contributes exactly one scalar
minus the sum of all edge coefficients. -/
theorem graphSourceBottom_offset (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℝ) :
    graphSourceBottom m left right J =
      finiteHeisenbergBottom (m + 1) left right J - ∑ e, J e := by
  have heq : graphSourceBottom m left right J = sourceMatrixBottom (m + 1)
      (finiteHeisenbergMatrix (m + 1) left right J - ((∑ e, J e : ℝ) : ℂ) • 1) := by
    unfold graphSourceBottom sourceMatrixBottom
    congr 1
    ext e
    constructor
    · rintro ⟨u, hu, rfl⟩
      let p : MediatorLowSpace (m + 1) := WithLp.toLp 2 u
      have hp : ‖p‖ = 1 := by
        have hsq : ‖p‖ ^ 2 = 1 := (sourceSpinMass_norm_sq p).symm.trans hu
        nlinarith [norm_nonneg p]
      exact ⟨p, hp, graphSourceForm_matrix m left right J p⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨fun s => p s, ?_, (graphSourceForm_matrix m left right J p).symm⟩
      rw [sourceSpinMass_norm_sq, hp]
      norm_num
  rw [heq, sourceMatrixBottom_shift]
  rfl

theorem graphSourceBottom_smul (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    graphSourceBottom m left right (fun e => a * J e) =
      a * (finiteHeisenbergBottom (m + 1) left right J - ∑ e, J e) := by
  rw [graphSourceBottom_offset, finiteHeisenbergBottom_smul _ _ _ _ ha, ← Finset.mul_sum]
  ring

theorem graphSourceBottom_bonds_smul {m r : ℕ} (F : MediatorIteration.Bonds (m + 1) r)
    {a : ℝ} (ha : 0 ≤ a) :
    graphSourceBottom m F.left F.right (fun e => a * (F.weight e : ℝ)) =
      a * (sourceMatrixBottom (m + 1) F.matrix - ∑ e, (F.weight e : ℝ)) := by
  rw [graphSourceBottom_smul m F.left F.right (fun e => (F.weight e : ℝ)) ha,
    finiteHeisenbergBottom_bonds]

end HubbardGlobal
end ContinuumCoulomb

end

end OAI
