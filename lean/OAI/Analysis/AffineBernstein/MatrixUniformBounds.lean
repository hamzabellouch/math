import Mathlib
import OAI.Analysis.AffineBernstein.PositiveMatrixTraceBound

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section MatrixUniformBounds
open Matrix
open scoped MatrixOrder

lemma posDef_lower_of_det_trace_bounds {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {c C : ℝ} (_hc : 0 < c) (hC : 0 ≤ C)
    (hdet : c ≤ A.det) (htr : A.trace ≤ C) :
    (A-(c/(C+1)^n) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  let a := hA.isHermitian.eigenvalues
  have ha (i : Fin n) : 0 < a i := hA.eigenvalues_pos i
  have hs : A.trace = ∑ i, a i := by simpa [a] using hA.isHermitian.trace_eq_sum_eigenvalues
  have hab (i : Fin n) : a i ≤ C :=
    (Finset.single_le_sum (fun j hj => (ha j).le) (Finset.mem_univ i)).trans (hs ▸ htr)
  have hd : A.det = ∏ i, a i := by simpa [a] using hA.isHermitian.det_eq_prod_eigenvalues
  have he (i : Fin n) : c/(C+1)^n ≤ a i := by
    have hp : (∏ j ∈ Finset.univ.erase i, a j) ≤ (C+1)^n := by
      calc
        _ ≤ ∏ j ∈ Finset.univ.erase i, (C+1) := Finset.prod_le_prod₀
          (fun j hj => (ha j).le) (fun j hj => by linarith [hab j])
        _ = (C+1)^(Finset.univ.erase i).card := by simp
        _ ≤ (C+1)^n := pow_le_pow_right₀ (by linarith) (by
          exact (Finset.card_le_card (Finset.erase_subset i Finset.univ)).trans_eq (by simp))
    have hmul := mul_le_mul_of_nonneg_left hp (ha i).le
    rw [Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i),← hd] at hmul
    exact (div_le_iff₀ (by positivity : 0 < (C+1)^n)).mpr (hdet.trans hmul)
  let U := hA.isHermitian.eigenvectorUnitary
  have hspec : A = (U:Matrix (Fin n) (Fin n) ℝ)*Matrix.diagonal a*(U:Matrix (Fin n) (Fin n) ℝ).conjTranspose := by
    simpa [U,a,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] using hA.isHermitian.spectral_theorem
  have hUU : (U:Matrix (Fin n) (Fin n) ℝ)*(U:Matrix (Fin n) (Fin n) ℝ).conjTranspose=1 :=
    Unitary.coe_mul_star_self U
  have hdpos : (Matrix.diagonal a-(c/(C+1)^n) • (1:Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
    have hh : Matrix.diagonal a-(c/(C+1)^n) • (1:Matrix (Fin n) (Fin n) ℝ) =
        Matrix.diagonal (fun i => a i-c/(C+1)^n) := by
      ext i j
      by_cases hij : i=j
      · subst j; simp
      · simp [Matrix.diagonal,hij]
    rw [hh,Matrix.posSemidef_diagonal_iff]
    intro i
    exact sub_nonneg.mpr (he i)
  have hh := hdpos.mul_mul_conjTranspose_same (U:Matrix (Fin n) (Fin n) ℝ)
  simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,hUU,← hspec] using hh

lemma posDef_quadratic_bounds {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hdet : c ≤ A.det) (htr : A.trace ≤ C) (p : Fin n → ℝ) :
    (c/(C+1)^n)*(∑ i, (p i)^2) ≤ p ⬝ᵥ (A*ᵥ p) ∧
      p ⬝ᵥ (A*ᵥ p) ≤ C*(∑ i, (p i)^2) := by
  constructor
  · have H := (posDef_lower_of_det_trace_bounds hA hc hC hdet htr).dotProduct_mulVec_nonneg p
    have he : p ⬝ᵥ ((A-(c/(C+1)^n) • (1:Matrix (Fin n) (Fin n) ℝ))*ᵥ p) =
        p ⬝ᵥ (A*ᵥ p)-(c/(C+1)^n)*(∑ i, (p i)^2) := by
      simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct,
        Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [star_trivial,he] at H
    exact sub_nonneg.mp H
  · exact (posSemidef_quadratic_le_trace_mul_sq hA.posSemidef p).trans
      (mul_le_mul_of_nonneg_right htr (Finset.sum_nonneg fun i hi => sq_nonneg _))

end MatrixUniformBounds


end
end AffineBernstein
end

end OAI
