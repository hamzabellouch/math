import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma adjugate_eq_det_smul_transpose' {Q : Matrix ι ι ℝ} (hQ : Q * Qᵀ = 1) :
    Q.adjugate = Q.det • Qᵀ := by
  calc
    Q.adjugate = Q.adjugate * (Q * Qᵀ) := by rw [hQ, Matrix.mul_one]
    _ = (Q.adjugate * Q) * Qᵀ := (Matrix.mul_assoc _ _ _).symm
    _ = Q.det • Qᵀ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

private lemma adjugate_conjugate_orthogonal' {Q : Matrix ι ι ℝ}
    (hQ : Q * Qᵀ = 1) (hQt : Qᵀ * Q = 1) (A : Matrix ι ι ℝ) :
    (Qᵀ * A * Q).adjugate = Qᵀ * A.adjugate * Q := by
  have hd : Q.det * Q.det = 1 := by
    have hh := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using hh
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    adjugate_eq_det_smul_transpose' hQ,
    adjugate_eq_det_smul_transpose' (Q := Qᵀ) (by simpa using hQt),
    Matrix.transpose_transpose, Matrix.det_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd, one_smul, Matrix.mul_assoc]

/- A coarse uniform bound for the sum of all principal cofactors by the
Jacobian of the identity-shifted positive semidefinite map. -/
lemma trace_adjugate_le_card_mul_det_add_one {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) :
    A.adjugate.trace ≤ (Fintype.card ι : ℝ) * (A + 1).det := by
  let Q : Matrix ι ι ℝ := hA.1.eigenvectorUnitary
  let d : ι → ℝ := hA.1.eigenvalues
  have hQ : Q * Qᵀ = 1 := by
    simpa only [Q, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (Unitary.coe_mul_star_self hA.1.eigenvectorUnitary)
  have hQt : Qᵀ * Q = 1 := by
    simpa only [Q, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (Unitary.coe_star_mul_self hA.1.eigenvectorUnitary)
  have hspec : A = Q * Matrix.diagonal d * Qᵀ := by
    simpa [Q,d,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hA.1.spectral_theorem
  have hdetQ : Q.det * Q.det = 1 := by
    have hh := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] using hh
  have htrace : A.adjugate.trace = ∑ i, ∏ j ∈ Finset.univ.erase i, d j := by
    rw [hspec]
    have had := adjugate_conjugate_orthogonal' (Q := Qᵀ) (by simpa using hQt) (by simpa using hQ) (Matrix.diagonal d)
    simp only [Matrix.transpose_transpose] at had
    rw [had]
    rw [Matrix.trace_mul_cycle,hQt,Matrix.one_mul,Matrix.adjugate_diagonal,Matrix.trace_diagonal]
  have hdet : (A + 1).det = ∏ i, (d i + 1) := by
    have hsum : A + 1 = Q * Matrix.diagonal (fun i => d i + 1) * Qᵀ := by
      have hdadd : Matrix.diagonal (fun i => d i + 1) = Matrix.diagonal d + 1 := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.diagonal,hij]
      rw [hdadd,Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,← hspec,hQ]
    rw [hsum,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,Matrix.det_diagonal]
    calc
      Q.det * (∏ i, (d i + 1)) * Q.det = (Q.det * Q.det) * ∏ i, (d i + 1) := by ring
      _ = _ := by rw [hdetQ,one_mul]
  rw [htrace,hdet]
  calc
    (∑ i, ∏ j ∈ Finset.univ.erase i, d j) ≤ ∑ _i : ι, ∏ j, (d j + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (∏ j ∈ Finset.univ.erase i, d j) ≤ ∏ j ∈ Finset.univ.erase i, (d j + 1) := by
          exact Finset.prod_le_prod₀ (fun index _ => hA.eigenvalues_nonneg index)
            (fun _ _ => by linarith)
        _ ≤ (d i + 1) * ∏ j ∈ Finset.univ.erase i, (d j + 1) := by
          have hp := Finset.prod_nonneg (s := Finset.univ.erase i)
            (fun j _ => add_nonneg (hA.eigenvalues_nonneg j) zero_le_one)
          nlinarith [hA.eigenvalues_nonneg i]
        _ = ∏ j, (d j + 1) := Finset.mul_prod_erase Finset.univ (fun j => d j + 1) (Finset.mem_univ i)
    _ = _ := by simp

end AffineBernstein
end

end OAI
