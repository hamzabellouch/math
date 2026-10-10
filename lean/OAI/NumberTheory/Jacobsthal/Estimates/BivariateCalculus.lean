import Mathlib

namespace OAI

namespace Erdos970

section

namespace ErdosImplicitCurvature

abbrev Bivariate := MvPolynomial (Fin 2) ℝ

noncomputable def peval (Q : Bivariate) (x y : ℝ) : ℝ :=
  MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else y) Q

noncomputable def partialX (Q : Bivariate) : Bivariate := MvPolynomial.pderiv 0 Q
noncomputable def partialY (Q : Bivariate) : Bivariate := MvPolynomial.pderiv 1 Q

@[simp] theorem peval_C (c x y : ℝ) : peval (MvPolynomial.C c) x y = c := by
  simp [peval]
@[simp] theorem peval_add (P Q : Bivariate) (x y : ℝ) :
    peval (P+Q) x y = peval P x y+peval Q x y := by simp [peval]
@[simp] theorem peval_mul (P Q : Bivariate) (x y : ℝ) :
    peval (P*Q) x y = peval P x y*peval Q x y := by simp [peval]
@[simp] theorem peval_X_zero (x y : ℝ) : peval (MvPolynomial.X 0) x y = x := by simp [peval]
@[simp] theorem peval_X_one (x y : ℝ) : peval (MvPolynomial.X 1) x y = y := by simp [peval]
@[simp] theorem peval_zero (x y : ℝ) : peval 0 x y = 0 := by simp [peval]
@[simp] theorem peval_one (x y : ℝ) : peval 1 x y = 1 := by simp [peval]

theorem mixed_partials (Q : Bivariate) : partialY (partialX Q) = partialX (partialY Q) := by
  classical
  ext m
  simp [partialX, partialY, MvPolynomial.coeff_pderiv,
    add_assoc, add_left_comm, add_comm, mul_left_comm, mul_comm]

theorem hasDerivAt_peval (Q : Bivariate) (u v : ℝ → ℝ) (du dv x : ℝ)
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x) :
    HasDerivAt (fun t => peval Q (u t) (v t))
      (peval (partialX Q) (u x) (v x)*du+peval (partialY Q) (u x) (v x)*dv) x := by
  induction Q using MvPolynomial.induction_on with
  | C c => simpa [partialX, partialY, MvPolynomial.pderiv_C] using hasDerivAt_const x c
  | add P Q hP hQ =>
      have h := (hP.add hQ).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun t => peval_add P Q (u t) (v t)))
      apply h.congr_deriv
      simp only [partialX, partialY, map_add, peval_add]
      ring
  | mul_X P i hP =>
      fin_cases i
      · have h := (hP.mul hu).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun t => show peval (P*MvPolynomial.X 0) (u t) (v t) =
            peval P (u t) (v t)*u t by simp))
        apply h.congr_deriv
        simp [partialX, partialY]
        ring
      · have h := (hP.mul hv).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun t => show peval (P*MvPolynomial.X 1) (u t) (v t) =
            peval P (u t) (v t)*v t by simp))
        apply h.congr_deriv
        simp [partialX, partialY]
        ring

theorem hasDerivAt_peval_graph (Q : Bivariate) (f : ℝ → ℝ) (df x : ℝ)
    (hf : HasDerivAt f df x) :
    HasDerivAt (fun t => peval Q t (f t))
      (peval (partialX Q) x (f x)+peval (partialY Q) x (f x)*df) x := by
  simpa using hasDerivAt_peval Q id f 1 df x (hasDerivAt_id x) hf

end ErdosImplicitCurvature

end

end Erdos970

end OAI
