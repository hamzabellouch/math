import OAI.Geometry.EinsteinFour.JacobiSymmetricKernel

namespace OAI

/-! Positivity of the curvature perturbation below the scalar conjugate
threshold. The cap three follows from positivity and trace three. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem three_sub_posSemidef {A : NormalMatrix} (hA : A.PosSemidef)
    (htr : A.trace = 3) : ((3 : ℝ) • (1 : NormalMatrix) - A).PosSemidef := by
  let U := hA.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ NormalMatrix U
  have hdiag : A = φ (diagonal hA.isHermitian.eigenvalues) := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.isHermitian.spectral_theorem
  have hsum : (∑ i, hA.isHermitian.eigenvalues i) = 3 := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq, htr] using
      hA.isHermitian.trace_eq_sum_eigenvalues.symm
  have hb (i : Fin 3) : hA.isHermitian.eigenvalues i ≤ 3 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hp : (diagonal (fun i => 3 - hA.isHermitian.eigenvalues i)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (hb i))
  have hφ : φ (diagonal (fun i => 3 - hA.isHermitian.eigenvalues i)) =
      (3 : ℝ) • (1 : NormalMatrix) - A := by
    have he : diagonal (fun i => 3 - hA.isHermitian.eigenvalues i) =
        (3 : ℝ) • (1 : NormalMatrix) - diagonal hA.isHermitian.eigenvalues := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [he, map_sub, map_smul, map_one, ← hdiag]
  rw [← hφ]
  simpa only [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose] using
    hp.conjTranspose_mul_mul_same (star (U : NormalMatrix))

theorem scalarLift_quadratic {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin 3 × Fin N → ℝ) :
    star x ⬝ᵥ (scalarLift G *ᵥ x) =
      ∑ a : Fin 3, star (fun i => x (a,i)) ⬝ᵥ (G *ᵥ fun i => x (a,i)) := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, scalarLift,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul,
    one_mul, zero_mul, star_trivial, Finset.mul_sum]
  simp

theorem scalarLift_posDef {N : ℕ} {G : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.PosDef) : (scalarLift G).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply scalarLift_conjTranspose
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hG.isHermitian.eq
  · intro x hx
    rw [scalarLift_quadratic]
    have hn : ∃ a : Fin 3, (fun i => x (a,i)) ≠ 0 := by
      by_contra! h
      apply hx
      funext p
      exact congrFun (h p.1) p.2
    obtain ⟨a,ha⟩ := hn
    exact Finset.sum_pos' (fun b _ => hG.posSemidef.dotProduct_mulVec_nonneg _)
      ⟨a, Finset.mem_univ _, hG.dotProduct_mulVec_pos ha⟩

theorem scalarLift_sub_three {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) :
    scalarLift (1 - (3 : ℝ) • G) = 1 - (3 : ℝ) • scalarLift G := by
  rw [← scalarLift_one N]
  ext ⟨a,i⟩ ⟨b,j⟩
  change (1 : NormalMatrix) a b * ((1 : Matrix (Fin N) (Fin N) ℝ) i j - 3 * G i j) =
    (1 : NormalMatrix) a b * (1 : Matrix (Fin N) (Fin N) ℝ) i j -
      3 * ((1 : NormalMatrix) a b * G i j)
  ring

theorem symmetricCurvatureKernel_one_sub_posDef {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G) (hSt : Sᵀ = S)
    (hscalar : (1 - (3 : ℝ) • G).PosDef)
    (R : Fin N → NormalMatrix) (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3) :
    (1 - symmetricCurvatureKernel S R).PosDef := by
  have hc := blockDiagonal_posSemidef (fun i => (3 : ℝ) • (1 : NormalMatrix) - R i)
    (fun i => three_sub_posSemidef (hR i).1 (hR i).2)
  have hb : Matrix.blockDiagonal (fun i => (3 : ℝ) • (1 : NormalMatrix) - R i) =
      (3 : ℝ) • 1 - Matrix.blockDiagonal R := by
    ext ⟨a,i⟩ ⟨b,j⟩
    by_cases hij : i = j
    · subst j
      simp [Matrix.blockDiagonal_apply, Matrix.one_apply]
    · simp [Matrix.blockDiagonal_apply, hij]
  rw [hb] at hc
  have hp := hc.conjTranspose_mul_mul_same (scalarLift S)
  rw [scalarLift_conjTranspose S hSt] at hp
  have h := (scalarLift_posDef hscalar).add_posSemidef hp
  have he : scalarLift (1 - (3 : ℝ) • G) + scalarLift S *
      ((3 : ℝ) • 1 - Matrix.blockDiagonal R) * scalarLift S =
      1 - symmetricCurvatureKernel S R := by
    rw [scalarLift_sub_three, symmetricCurvatureKernel,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, ← scalarLift_mul, hS]
    module
  rwa [he] at h

end
end PositiveEinsteinFour.Jacobi

end OAI
