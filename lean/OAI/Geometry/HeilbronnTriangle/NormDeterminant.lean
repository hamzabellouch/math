import OAI.Geometry.HeilbronnTriangle.NormPolynomial

namespace OAI

noncomputable section

namespace Problem355.NormDeterminant

open Matrix
open scoped BigOperators

abbrev Variables (ι : Type*) := Fin 3 × Fin 3 × ι

variable {ι K : Type*} [Fintype ι] [Field K]

def coordinateForm (β : ι → K) (j i : Fin 3) : MvPolynomial (Variables ι) K :=
  ∑ ν, MvPolynomial.C (β ν) * MvPolynomial.X (j, i, ν)

def determinantPolynomial (β : ι → K) : MvPolynomial (Variables ι) K :=
  Matrix.det (Matrix.of (fun i j => coordinateForm β j i))

def groupRename (e : Equiv.Perm (Fin 3)) (v : Variables ι) : Variables ι :=
  (e v.1, v.2)

@[simp] theorem rename_coordinateForm (β : ι → K) (e : Equiv.Perm (Fin 3))
    (j i : Fin 3) :
    MvPolynomial.rename (groupRename (ι := ι) e) (coordinateForm β j i) =
      coordinateForm β (e j) i := by
  simp [coordinateForm, groupRename]

theorem rename_determinantPolynomial (β : ι → K) (e : Equiv.Perm (Fin 3)) :
    MvPolynomial.rename (groupRename (ι := ι) e) (determinantPolynomial β) =
      Equiv.Perm.sign e * determinantPolynomial β := by
  rw [determinantPolynomial, AlgHom.map_det]
  change Matrix.det (Matrix.of (fun i j =>
    MvPolynomial.rename (groupRename (ι := ι) e) (coordinateForm β j i))) = _
  simp_rw [rename_coordinateForm]
  exact Matrix.det_permute' e (Matrix.of (fun i j => coordinateForm β j i))

theorem swap_determinantPolynomial (β : ι → K) {a b : Fin 3} (hab : a ≠ b) :
    MvPolynomial.rename (groupRename (ι := ι) (Equiv.swap a b))
      (determinantPolynomial β) = -determinantPolynomial β := by
  rw [rename_determinantPolynomial, Equiv.Perm.sign_swap hab]
  simp

theorem eval_determinantPolynomial (β : ι → K) (x : Variables ι → K) :
    MvPolynomial.eval x (determinantPolynomial β) =
      Matrix.det (Matrix.of (fun i j => ∑ ν, β ν * x (j, i, ν))) := by
  rw [determinantPolynomial, RingHom.map_det]
  congr 1
  ext i j
  simp [coordinateForm, RingHom.mapMatrix_apply]

variable {F : Type*} [Field F] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]

def normDeterminantPolynomial (β : ι → K) : MvPolynomial (Variables ι) F :=
  NormPolynomial.normPolynomial (F := F) (determinantPolynomial β)

theorem swap_normDeterminantPolynomial (β : ι → K)
    (hodd : Odd (Module.finrank F K)) {a b : Fin 3} (hab : a ≠ b) :
    MvPolynomial.rename (groupRename (ι := ι) (Equiv.swap a b))
      (normDeterminantPolynomial (F := F) β) =
        -normDeterminantPolynomial (F := F) β :=
  NormPolynomial.rename_normPolynomial_of_odd hodd _ _
    (swap_determinantPolynomial β hab)

def matrixCoordinates (b : Module.Basis ι F K) (A : Matrix (Fin 3) (Fin 3) K)
    (v : Variables ι) : F :=
  b.repr (A v.2.1 v.1) v.2.2

omit [FiniteDimensional F K] [IsGalois F K] in

theorem eval_determinantPolynomial_matrixCoordinates (b : Module.Basis ι F K)
    (A : Matrix (Fin 3) (Fin 3) K) :
    MvPolynomial.eval (algebraMap F K ∘ matrixCoordinates b A)
      (determinantPolynomial b) = A.det := by
  rw [eval_determinantPolynomial]
  congr 1
  ext i j
  simpa [matrixCoordinates, Function.comp_def, Algebra.smul_def, mul_comm] using
    b.sum_repr (A i j)

theorem eval_normDeterminantPolynomial_matrixCoordinates (b : Module.Basis ι F K)
    (A : Matrix (Fin 3) (Fin 3) K) :
    MvPolynomial.eval (matrixCoordinates b A)
      (normDeterminantPolynomial (F := F) b) = Algebra.norm F A.det := by
  rw [normDeterminantPolynomial, NormPolynomial.eval_normPolynomial,
    eval_determinantPolynomial_matrixCoordinates]

theorem eval_normDeterminantPolynomial_ne_zero (b : Module.Basis ι F K)
    {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    MvPolynomial.eval (matrixCoordinates b (NormFoundation.momentMatrix x y z))
      (normDeterminantPolynomial (F := F) b) ≠ 0 := by
  rw [eval_normDeterminantPolynomial_matrixCoordinates]
  exact NormFoundation.norm_det_momentMatrix_ne_zero hxy hxz hyz

def labelCoordinates (b : Module.Basis ι F K) (x : K) (v : Fin 3 × ι) : F :=
  b.repr (NormFoundation.momentColumn x v.1) v.2

def labelTriple (b : Module.Basis ι F K) (x y z : K) (v : Variables ι) : F :=
  labelCoordinates b (![x, y, z] v.1) v.2

omit [Fintype ι] [FiniteDimensional F K] [IsGalois F K] in
theorem labelTriple_eq_matrixCoordinates (b : Module.Basis ι F K) (x y z : K) :
    labelTriple b x y z = matrixCoordinates b (NormFoundation.momentMatrix x y z) := by
  funext v
  rcases v with ⟨j, i, ν⟩
  fin_cases j <;> fin_cases i <;>
    simp [labelTriple, labelCoordinates, matrixCoordinates,
      NormFoundation.momentColumn, NormFoundation.momentMatrix]

theorem eval_normDeterminantPolynomial_labels_ne_zero (b : Module.Basis ι F K)
    {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    MvPolynomial.eval (labelTriple b x y z)
      (normDeterminantPolynomial (F := F) b) ≠ 0 := by
  rw [labelTriple_eq_matrixCoordinates]
  exact eval_normDeterminantPolynomial_ne_zero b hxy hxz hyz

end Problem355.NormDeterminant

end

end OAI
