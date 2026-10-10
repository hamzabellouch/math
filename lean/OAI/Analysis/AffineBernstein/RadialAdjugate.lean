import Mathlib
import OAI.Analysis.AffineBernstein.BlockNewton

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma adjugate_block_radial (R : Matrix ι ι ℝ) :
    (Matrix.fromBlocks R 0 0 (0 : Matrix Unit Unit ℝ)).adjugate =
      Matrix.fromBlocks 0 0 0 (R.det • (1 : Matrix Unit Unit ℝ)) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hh := adjugate_fromBlocks_scalar R 0 i j
      simpa using hh
    | inr j =>
      cases j
      rw [Matrix.adjugate_apply]
      apply Matrix.det_eq_zero_of_column_eq_zero (Sum.inr ())
      intro l
      cases l <;> simp [Matrix.updateRow_apply,Matrix.fromBlocks]
  | inr i =>
    cases i
    cases j with
    | inl j =>
      rw [Matrix.adjugate_apply]
      apply Matrix.det_eq_zero_of_row_eq_zero (Sum.inr ())
      intro l
      cases l <;> simp [Matrix.updateRow_apply,Matrix.fromBlocks]
    | inr j =>
      cases j
      rw [Matrix.adjugate_apply]
      have hh : (Matrix.fromBlocks R 0 0 (0 : Matrix Unit Unit ℝ)).updateRow
          (Sum.inr ()) (Pi.single (Sum.inr ()) 1) = Matrix.fromBlocks R 0 0 (1 : Matrix Unit Unit ℝ) := by
        ext l m
        cases l <;> cases m <;> simp [Matrix.updateRow_apply,Matrix.fromBlocks]
      rw [hh,Matrix.det_fromBlocks_zero₂₁]
      simp

def radialShear (e : ι ⊕ Unit → ℝ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  Matrix.fromBlocks 1 (Matrix.of fun i _ => e (Sum.inl i)) 0 1

lemma radialShear_det (e : ι ⊕ Unit → ℝ) : (radialShear e).det = 1 := by
  rw [radialShear,Matrix.det_fromBlocks_zero₂₁]
  simp

omit [Fintype ι] in
lemma radialShear_last (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1) (i : ι ⊕ Unit) :
    radialShear e i (Sum.inr ()) = e i := by
  cases i <;> simp [radialShear,Matrix.fromBlocks,he]

lemma mul_radialShear_left (A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (e : ι ⊕ Unit → ℝ) (i : ι ⊕ Unit) (j : ι) :
    (A * radialShear e) i (Sum.inl j) = A i (Sum.inl j) := by
  simp [Matrix.mul_apply,Fintype.sum_sum_type,radialShear,Matrix.fromBlocks,Matrix.one_apply]

lemma transpose_radialShear_mul_left (A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (e : ι ⊕ Unit → ℝ) (i : ι) (j : ι ⊕ Unit) :
    ((radialShear e)ᵀ * A) (Sum.inl i) j = A (Sum.inl i) j := by
  simp [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_sum_type,radialShear,
    Matrix.fromBlocks,Matrix.one_apply]

lemma mul_radialShear_last (A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1) (i : ι ⊕ Unit) :
    (A * radialShear e) i (Sum.inr ()) = (A *ᵥ e) i := by
  simp only [Matrix.mul_apply,radialShear_last e he,Matrix.mulVec, dotProduct]

lemma radialShear_conjugate {A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hA : A.IsSymm) (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1)
    (hz : A *ᵥ e = 0) :
    (radialShear e)ᵀ * A * radialShear e =
      Matrix.fromBlocks (A.submatrix Sum.inl Sum.inl) 0 0 (0 : Matrix Unit Unit ℝ) := by
  have hs : ((radialShear e)ᵀ * A * radialShear e).IsSymm := by
    simp only [Matrix.IsSymm,Matrix.transpose_mul,Matrix.transpose_transpose,hA.eq,Matrix.mul_assoc]
  have hlast (i : ι ⊕ Unit) : ((radialShear e)ᵀ * A * radialShear e) i (Sum.inr ()) = 0 := by
    rw [Matrix.mul_assoc,Matrix.mul_apply]
    simp [mul_radialShear_last A e he,hz]
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rw [Matrix.mul_assoc,transpose_radialShear_mul_left,mul_radialShear_left]
      rfl
    | inr j => cases j; exact hlast _
  | inr i =>
    cases i
    cases j with
    | inl j => rw [← hs.apply]; exact hlast _
    | inr j => cases j; exact hlast _

/- A symmetric form with radial null vector has its full adjugate equal to
its transverse principal minor times the radial outer product. This includes
all empty transverse blocks and needs no invertibility of the full matrix. -/
theorem radial_adjugate {A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hA : A.IsSymm) (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1)
    (hz : A *ᵥ e = 0) (i j : ι ⊕ Unit) :
    A.adjugate i j = (A.submatrix Sum.inl Sum.inl).det * e i * e j := by
  let P := radialShear e
  let d := (A.submatrix Sum.inl Sum.inl).det
  have hP : P.det = 1 := radialShear_det e
  have hp : P * P.adjugate = 1 := by rw [Matrix.mul_adjugate,hP,one_smul]
  have hpt : (Pᵀ).adjugate * Pᵀ = 1 := by
    rw [Matrix.adjugate_mul,Matrix.det_transpose,hP,one_smul]
  have hh := congrArg Matrix.adjugate (radialShear_conjugate hA e he hz)
  rw [adjugate_block_radial,Matrix.adjugate_mul_distrib,Matrix.adjugate_mul_distrib] at hh
  have hmul := congrArg (fun M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ => P*M*Pᵀ) hh
  change P * (P.adjugate * (A.adjugate * (Pᵀ).adjugate)) * Pᵀ =
    P*Matrix.fromBlocks 0 0 0 (d • (1 : Matrix Unit Unit ℝ))*Pᵀ at hmul
  have heq : A.adjugate = P*Matrix.fromBlocks 0 0 0 (d • (1 : Matrix Unit Unit ℝ))*Pᵀ := by
    calc
      _ = (P*P.adjugate)*A.adjugate*((Pᵀ).adjugate*Pᵀ) := by rw [hp,hpt,Matrix.one_mul,Matrix.mul_one]
      _ = _ := by simpa only [Matrix.mul_assoc] using hmul
  rw [heq]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero,zero_add,
    Fintype.sum_unique,Matrix.smul_apply,Matrix.one_apply,ite_true,smul_eq_mul,mul_one]
  change (P i (Sum.inr ()) * d)*P j (Sum.inr ()) = _
  dsimp only [P,d]
  rw [radialShear_last e he,radialShear_last e he]
  ring

lemma radial_adjugate_trace {A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hA : A.IsSymm) (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1)
    (hz : A *ᵥ e = 0) :
    A.adjugate.trace = (A.submatrix Sum.inl Sum.inl).det * ∑ i, e i * e i := by
  simp only [Matrix.trace,Matrix.diag,radial_adjugate hA e he hz,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end AffineBernstein
end

end OAI
