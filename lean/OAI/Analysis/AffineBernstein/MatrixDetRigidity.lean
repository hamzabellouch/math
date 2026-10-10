import Mathlib
import OAI.Analysis.AffineBernstein.AffineFamily

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Matrix
open scoped MatrixOrder

lemma posSemidef_det_one_add_eq_zero {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosSemidef) (hdet : (1+P).det=1) : P=0 := by
  classical
  let a := hP.isHermitian.eigenvalues
  let U := hP.isHermitian.eigenvectorUnitary
  have ha (i : Fin n) : 0 ≤ a i := hP.eigenvalues_nonneg i
  have hspec : P = (U:Matrix (Fin n) (Fin n) ℝ)*Matrix.diagonal a*(U:Matrix (Fin n) (Fin n) ℝ).conjTranspose := by
    simpa [U,a,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] using hP.isHermitian.spectral_theorem
  have hUU : (U:Matrix (Fin n) (Fin n) ℝ)*(U:Matrix (Fin n) (Fin n) ℝ).conjTranspose=1 :=
    Unitary.coe_mul_star_self U
  have hds : Matrix.diagonal (fun i => 1+a i) = (1:Matrix (Fin n) (Fin n) ℝ)+Matrix.diagonal a := by
    ext i j
    by_cases hij : i=j
    · subst j; simp
    · simp [Matrix.diagonal,hij]
  have hs1 : 1+P=(U:Matrix (Fin n) (Fin n) ℝ)*Matrix.diagonal (fun i => 1+a i)*(U:Matrix (Fin n) (Fin n) ℝ).conjTranspose := by
    rw [hds,Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,hUU,← hspec]
  have hprod : (∏ i, (1+a i))=1 := by
    rw [hs1,Matrix.det_mul,Matrix.det_mul,Matrix.det_diagonal] at hdet
    have hUUd := congrArg Matrix.det hUU
    rw [Matrix.det_mul,Matrix.det_one] at hUUd
    nlinarith only [hdet,hUUd]
  have ha0 (i : Fin n) : a i=0 := by
    have hrest : 1 ≤ ∏ j ∈ Finset.univ.erase i, (1+a j) :=
      Finset.one_le_prod₀ (fun index _ => by linarith [ha index])
    have hmul := mul_le_mul_of_nonneg_left hrest (by linarith [ha i] : 0 ≤ 1+a i)
    rw [mul_one,Finset.mul_prod_erase Finset.univ (fun j => 1+a j) (Finset.mem_univ i),hprod] at hmul
    linarith [ha i]
  have hae : a=0 := funext ha0
  rw [hspec,hae]
  simp

lemma posDef_eq_of_posSemidef_sub_det_eq {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hBA : (B-A).PosSemidef) (hdet : B.det=A.det) : B=A := by
  classical
  let S := CFC.sqrt A
  have hS : S.conjTranspose=S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hSS : S*S=A := by simpa only [S,pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hSd : S.det ≠ 0 := by
    have hd := congrArg Matrix.det hSS
    rw [Matrix.det_mul] at hd
    intro H
    rw [H,zero_mul] at hd
    exact hA.det_pos.ne' hd.symm
  have hSI : S⁻¹*S=1 := Matrix.nonsing_inv_mul S (isUnit_iff_ne_zero.mpr hSd)
  have hIS : S*S⁻¹=1 := Matrix.mul_nonsing_inv S (isUnit_iff_ne_zero.mpr hSd)
  have hI : (S⁻¹).conjTranspose=S⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv,hS]
  have he : S⁻¹*A*S⁻¹=1 := by
    rw [← hSS]
    calc
      _ = (S⁻¹*S)*(S*S⁻¹) := by noncomm_ring
      _ = 1 := by rw [hSI,hIS,Matrix.one_mul]
  let P := S⁻¹*(B-A)*S⁻¹
  have hP : P.PosSemidef := by
    simpa only [hI] using hBA.mul_mul_conjTranspose_same S⁻¹
  have hEP : 1+P=S⁻¹*B*S⁻¹ := by
    dsimp [P]
    rw [Matrix.mul_sub,Matrix.sub_mul,he]
    abel
  have hPD : (1+P).det=1 := by
    rw [hEP,Matrix.det_mul,Matrix.det_mul,hdet]
    simpa only [Matrix.det_mul,Matrix.det_one] using congrArg Matrix.det he
  have hP0 := posSemidef_det_one_add_eq_zero hP hPD
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => S*M*S) hP0
  have hc : S*P*S=B-A := by
    dsimp [P]
    calc
      _ = (S*S⁻¹)*(B-A)*(S⁻¹*S) := by noncomm_ring
      _ = B-A := by rw [hIS,hSI,Matrix.one_mul,Matrix.mul_one]
  rw [hc,Matrix.mul_zero,Matrix.zero_mul] at hh
  exact sub_eq_zero.mp hh

end AffineBernstein

end

end OAI
