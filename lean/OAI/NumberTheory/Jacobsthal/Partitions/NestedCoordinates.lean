import Mathlib

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

variable (R : Type*) [CommSemiring R]

abbrev MV := MvPolynomial (Fin 2) R
abbrev Nested := Polynomial (Polynomial R)

noncomputable def nestedX : MV R ≃ₐ[R] Nested R :=
  (MvPolynomial.finSuccEquiv R 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1)))

noncomputable def nestedY : MV R ≃ₐ[R] Nested R :=
  (MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1)).trans (nestedX R)

@[simp] theorem nestedX_C (c : R) : nestedX R (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) := by
  simpa using (nestedX R).commutes c

@[simp] theorem nestedX_X_zero : nestedX R (MvPolynomial.X 0) = Polynomial.X := by
  simp [nestedX, Polynomial.coe_mapAlgEquiv, MvPolynomial.finSuccEquiv_X_zero]

@[simp] theorem nestedX_X_one : nestedX R (MvPolynomial.X 1) = Polynomial.C Polynomial.X := by
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 (MvPolynomial.X (Fin.succ (0 : Fin 1)))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp [MvPolynomial.uniqueAlgEquiv_apply]

@[simp] theorem nestedY_C (c : R) : nestedY R (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) := by
  simp [nestedY]

@[simp] theorem nestedY_X_zero : nestedY R (MvPolynomial.X 0) = Polynomial.C Polynomial.X := by
  simp [nestedY]

@[simp] theorem nestedY_X_one : nestedY R (MvPolynomial.X 1) = Polynomial.X := by
  simp [nestedY]

noncomputable def nestedEvalHom (x y : R) : Nested R →+* R :=
  (Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (Polynomial.evalRingHom x))

@[simp] theorem nestedEvalHom_C (p : Polynomial R) (x y : R) :
    nestedEvalHom R x y (Polynomial.C p) = p.eval x := by simp [nestedEvalHom]

@[simp] theorem nestedEvalHom_X (x y : R) :
    nestedEvalHom R x y Polynomial.X = y := by simp [nestedEvalHom]

theorem eval_nestedY (Q : MV R) (x y : R) :
    nestedEvalHom R x y (nestedY R Q) = MvPolynomial.eval ![x,y] Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [nestedEvalHom]
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P i hP =>
      fin_cases i
      · simp [map_mul, hP]
      · simp [map_mul, hP]

theorem eval_nestedX (Q : MV R) (x y : R) :
    nestedEvalHom R y x (nestedX R Q) = MvPolynomial.eval ![x,y] Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [nestedEvalHom]
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P i hP =>
      fin_cases i
      · simp [map_mul, hP]
      · simp [map_mul, hP]

end ErdosCriticalGeometry

end

end Erdos970

end OAI
