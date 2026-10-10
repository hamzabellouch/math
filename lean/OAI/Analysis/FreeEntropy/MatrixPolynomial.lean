import OAI.Analysis.FreeEntropy.ComplexPolynomialFunctions

namespace OAI

universe u1 u2 u3

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
 abbrev MatrixIndex (n d : ℕ) := Fin n × Fin d × Fin d
 def coordinateMatrix {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) : Matrix (Fin d) (Fin d) ℂ :=
  hermitianMatrix (WithLp.toLp 2 x) i
 theorem coordinateMatrix_polynomial {n d : ℕ} (i : Fin n) (j k : Fin d) :
    IsComplexPolynomial (fun x : MatrixIndex n d → ℝ => coordinateMatrix x i j k) := by
  unfold coordinateMatrix hermitianMatrix
  split_ifs
  · exact IsComplexPolynomial.coord _
  · simpa only [div_eq_mul_inv, mul_comm, WithLp.ofLp_toLp] using ((IsComplexPolynomial.coord (i,j,k)).add ((IsComplexPolynomial.coord (i,k,j)).const_mul Complex.I)).mul_const ((Real.sqrt 2 : ℂ)⁻¹)
  · simpa only [div_eq_mul_inv, mul_comm, WithLp.ofLp_toLp] using ((IsComplexPolynomial.coord (i,k,j)).sub ((IsComplexPolynomial.coord (i,j,k)).const_mul Complex.I)).mul_const ((Real.sqrt 2 : ℂ)⁻¹)
 theorem coordinateMatrix_update {n d : ℕ} (x : MatrixIndex n d → ℝ) (q : MatrixIndex n d) (t : ℝ) (i : Fin n) :
    coordinateMatrix (Function.update x q t) i = coordinateMatrix x i +
      (t-x q) • (if q.1=i then hermitianBasis q.2.1 q.2.2 else 0) := by
  have he : (WithLp.toLp 2 (Function.update x q t) : MatrixCoordinates n d) =
      WithLp.toLp 2 x + (t-x q) • EuclideanSpace.single q 1 := by
    ext a
    by_cases h : a=q
    · subst a; simp
    · simp [EuclideanSpace.single, h]
  unfold coordinateMatrix
  rw [he, hermitianMatrix_add, hermitianMatrix_smul, hermitianMatrix_single]
 theorem coordinateMatrix_hasDeriv {n d : ℕ} (x : MatrixIndex n d → ℝ) (q : MatrixIndex n d) (i : Fin n) (j k : Fin d) :
    HasDerivAt (fun t => coordinateMatrix (Function.update x q t) i j k)
      ((if q.1=i then hermitianBasis q.2.1 q.2.2 else 0) j k) (x q) := by
  let D : Matrix (Fin d) (Fin d) ℂ := if q.1=i then hermitianBasis q.2.1 q.2.2 else 0
  have hd : HasDerivAt (fun t : ℝ => coordinateMatrix x i j k + ((t-x q : ℝ) : ℂ)*(D j k)) (D j k) (x q) := by
    simpa using ((((hasDerivAt_id (x q)).sub_const (x q)).ofReal_comp.mul_const (D j k)).const_add (coordinateMatrix x i j k))
  convert hd using 1 ; try rfl
  funext t
  rw [coordinateMatrix_update]
  by_cases he : q.1=i <;> simp [he, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, D]
 variable {ι : Type u1} {κ : Type u2} {d : Type u3} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
 def IsMatrixPolynomial (A : (ι → ℝ) → Matrix d d ℂ) : Prop := ∀ j k, IsComplexPolynomial (fun x => A x j k)
 namespace IsMatrixPolynomial
 theorem const {ι : Type u1} {d : Type u3} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) : IsMatrixPolynomial (fun _ : ι → ℝ => A) := fun _ _ => IsComplexPolynomial.const _
 theorem add {ι : Type u1} {d : Type u3} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {A B : (ι → ℝ) → Matrix d d ℂ} (hA : IsMatrixPolynomial A) (hB : IsMatrixPolynomial B) :
    IsMatrixPolynomial (fun x => A x+B x) := fun j k => (hA j k).add (hB j k)
 theorem mul {ι : Type u1} {d : Type u3} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {A B : (ι → ℝ) → Matrix d d ℂ} (hA : IsMatrixPolynomial A) (hB : IsMatrixPolynomial B) :
    IsMatrixPolynomial (fun x => A x*B x) := by
  intro j k
  exact IsComplexPolynomial.finset_sum univ (fun l _ => (hA j l).mul (hB l k))
 theorem smul {ι : Type u1} {d : Type u3} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {A : (ι → ℝ) → Matrix d d ℂ} (hA : IsMatrixPolynomial A) (c : ℂ) :
    IsMatrixPolynomial (fun x => c • A x) := fun j k => (hA j k).const_mul c
 theorem trace {ι : Type u1} {d : Type u3} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {A : (ι → ℝ) → Matrix d d ℂ} (hA : IsMatrixPolynomial A) :
    IsComplexPolynomial (fun x => Matrix.trace (A x)) :=
  IsComplexPolynomial.finset_sum univ (fun j _ => hA j j)
 theorem word {A : κ → (ι → ℝ) → Matrix d d ℂ} (hA : ∀ i, IsMatrixPolynomial (A i)) (w : List κ) :
    IsMatrixPolynomial (fun x => (w.map (fun i => A i x)).prod) := by
  induction w with
  | nil => exact const 1
  | cons i w ih => exact (hA i).mul ih
 end IsMatrixPolynomial
 theorem hasDerivAt_matrix_mul {d : Type u3} [Fintype d] [DecidableEq d] {A B : ℝ → Matrix d d ℂ} {A' B' : Matrix d d ℂ} {t : ℝ}
    (hA : ∀ j k, HasDerivAt (fun s => A s j k) (A' j k) t)
    (hB : ∀ j k, HasDerivAt (fun s => B s j k) (B' j k) t) :
    ∀ j k, HasDerivAt (fun s => (A s*B s) j k) ((A'*B t+A t*B') j k) t := by
  intro j k
  have hd := HasDerivAt.sum (u := univ) (fun l _ => (hA j l).mul (hB l k))
  simpa [Matrix.mul_apply, sum_add_distrib, Matrix.add_apply, Finset.sum_fn] using hd
end FiniteEntropySeparation

end

end OAI
