import OAI.AlgebraicGeometry.StableCoordinate.Definitions
import OAI.AlgebraicGeometry.StableCoordinate.MatrixChange
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases

namespace OAI

/-!
# Polynomial presentation, with arbitrary additional independent variables

The source variables in `P n` are `p,s,u,F,J`, in that order, followed by
`n` independent variables.  The matrix transformation leaves those extra
variables fixed.  In particular `n=0` gives the unstabilized presentation and
`n=1` supplies the presentation needed in the one-variable stabilization.
-/

namespace StableCoordinate.Presentation

open MvPolynomial MatrixChange

noncomputable section

abbrev P (n : ℕ) := R (5 + n)

def p (n : ℕ) : P n := X ((0 : Fin 5).castAdd n)
def s (n : ℕ) : P n := X ((1 : Fin 5).castAdd n)
def u (n : ℕ) : P n := X ((2 : Fin 5).castAdd n)
def F (n : ℕ) : P n := X ((3 : Fin 5).castAdd n)
def J (n : ℕ) : P n := X ((4 : Fin 5).castAdd n)
def x (n : ℕ) : P n := quad (p n) (s n) (u n) (F n)
def H (n : ℕ) : P n := relation (p n) (s n) (u n) (F n) (J n)
def relationIdeal (n : ℕ) : Ideal (P n) := Ideal.span {H n}
abbrev A (n : ℕ) := P n ⧸ relationIdeal n

def changeCoords (n : ℕ) (t : ℂ) : Fin 5 → P n :=
  ![pChange (C t) (p n) (s n) (u n) (F n) (J n),
    sChange (C t) (p n) (s n) (u n) (F n) (J n),
    uChange (C t) (p n) (s n) (u n) (F n) (J n),
    FChange (C t) (p n) (s n) (u n) (F n) (J n), J n]

def changeHom (n : ℕ) (t : ℂ) : P n →ₐ[ℂ] P n :=
  aeval (Fin.addCases (changeCoords n t) (fun i : Fin n => X (i.natAdd 5)))

@[simp] lemma changeHom_C (n : ℕ) (t c : ℂ) : changeHom n t (C c) = C c := by
  simp [changeHom]

@[simp] lemma changeHom_X_left (n : ℕ) (t : ℂ) (i : Fin 5) :
    changeHom n t (X (i.castAdd n)) = changeCoords n t i := by
  simp [changeHom]

@[simp] lemma changeHom_X_right (n : ℕ) (t : ℂ) (i : Fin n) :
    changeHom n t (X (i.natAdd 5)) = X (i.natAdd 5) := by
  simp [changeHom]

@[simp] lemma changeHom_p (n : ℕ) (t : ℂ) :
    changeHom n t (p n) = pChange (C t) (p n) (s n) (u n) (F n) (J n) := by
  simp [p, changeCoords]
@[simp] lemma changeHom_s (n : ℕ) (t : ℂ) :
    changeHom n t (s n) = sChange (C t) (p n) (s n) (u n) (F n) (J n) := by
  simp [s, changeCoords]
@[simp] lemma changeHom_u (n : ℕ) (t : ℂ) :
    changeHom n t (u n) = uChange (C t) (p n) (s n) (u n) (F n) (J n) := by
  simp [u, changeCoords]
@[simp] lemma changeHom_F (n : ℕ) (t : ℂ) :
    changeHom n t (F n) = FChange (C t) (p n) (s n) (u n) (F n) (J n) := by
  simp [F, changeCoords]
@[simp] lemma changeHom_J (n : ℕ) (t : ℂ) : changeHom n t (J n) = J n := by
  simp [J, changeCoords]

lemma changeHom_comp (n : ℕ) (t r : ℂ) :
    (changeHom n t).comp (changeHom n r) = changeHom n (r + t) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;>
      simp [AlgHom.comp_apply, changeCoords,
        pChange_add, sChange_add, uChange_add, FChange_add, map_add]
  · simp

lemma changeHom_zero (n : ℕ) : changeHom n 0 = AlgHom.id ℂ (P n) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> simp [changeCoords, p, s, u, F, J]
  · simp

/-- The source's inverse matrix substitution, regarded as an algebra automorphism.
It carries the original hypersurface equation to `-J-u`. -/
def matrixEquiv (n : ℕ) : P n ≃ₐ[ℂ] P n :=
  AlgEquiv.ofAlgHom (changeHom n (-1)) (changeHom n 1)
    (by rw [changeHom_comp]; simpa using changeHom_zero n)
    (by rw [changeHom_comp]; simpa using changeHom_zero n)

@[simp] lemma matrixEquiv_apply (n : ℕ) (v : P n) :
    matrixEquiv n v = changeHom n (-1) v := rfl

@[simp] lemma matrixEquiv_symm_apply (n : ℕ) (v : P n) :
    (matrixEquiv n).symm v = changeHom n 1 v := rfl

lemma matrixEquiv_H (n : ℕ) : matrixEquiv n (H n) = -J n - u n := by
  simp [H, relation_change_neg_one]

lemma matrixEquiv_x (n : ℕ) : matrixEquiv n (x n) = x n := by
  simp [x, quad_change]


/-- Set the transformed variable `u` equal to `-J` and retain all other variables. -/
def eliminateHom (n : ℕ) : P n →ₐ[ℂ] R (4 + n) :=
  aeval (Fin.addCases
    ![X ((0 : Fin 4).castAdd n), X ((1 : Fin 4).castAdd n),
      -X ((3 : Fin 4).castAdd n), X ((2 : Fin 4).castAdd n), X ((3 : Fin 4).castAdd n)]
    (fun i : Fin n => X (i.natAdd 4)))

/-- Include the four retained variables and all the extra variables. -/
def includeHom (n : ℕ) : R (4 + n) →ₐ[ℂ] P n :=
  aeval (Fin.addCases ![p n, s n, F n, J n] (fun i : Fin n => X (i.natAdd 5)))

@[simp] lemma eliminateHom_p (n : ℕ) : eliminateHom n (p n) = X ((0 : Fin 4).castAdd n) := by
  simp [eliminateHom, p]
@[simp] lemma eliminateHom_s (n : ℕ) : eliminateHom n (s n) = X ((1 : Fin 4).castAdd n) := by
  simp [eliminateHom, s]
@[simp] lemma eliminateHom_u (n : ℕ) : eliminateHom n (u n) = -X ((3 : Fin 4).castAdd n) := by
  simp [eliminateHom, u]
@[simp] lemma eliminateHom_F (n : ℕ) : eliminateHom n (F n) = X ((2 : Fin 4).castAdd n) := by
  simp [eliminateHom, F]
@[simp] lemma eliminateHom_J (n : ℕ) : eliminateHom n (J n) = X ((3 : Fin 4).castAdd n) := by
  simp [eliminateHom, J]

@[simp] lemma eliminateHom_X_right (n : ℕ) (i : Fin n) :
    eliminateHom n (X (i.natAdd 5)) = X (i.natAdd 4) := by
  simp [eliminateHom]
@[simp] lemma includeHom_X_right (n : ℕ) (i : Fin n) :
    includeHom n (X (i.natAdd 4)) = X (i.natAdd 5) := by
  simp [includeHom]

lemma eliminateHom_includeHom (n : ℕ) :
    (eliminateHom n).comp (includeHom n) = AlgHom.id ℂ (R (4+n)) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> simp [includeHom]
  · simp

/-- Quotient projection for the source hypersurface. -/
def mk (n : ℕ) : P n →ₐ[ℂ] A n := Ideal.Quotient.mkₐ ℂ (relationIdeal n)

@[simp] lemma mk_H (n : ℕ) : mk n (H n) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)

/-- Evaluation in the explicit four-variable polynomial presentation. -/
def polynomialMap (n : ℕ) : P n →ₐ[ℂ] R (4+n) :=
  (eliminateHom n).comp (matrixEquiv n).toAlgHom

@[simp] lemma polynomialMap_H (n : ℕ) : polynomialMap n (H n) = 0 := by
  change eliminateHom n (matrixEquiv n (H n)) = 0
  rw [matrixEquiv_H]
  simp

/-- The source quotient maps to the four-variable polynomial presentation. -/
def toPolynomial (n : ℕ) : A n →ₐ[ℂ] R (4+n) :=
  Ideal.Quotient.liftₐ (relationIdeal n) (polynomialMap n) (by
    apply (Ideal.span_singleton_le_iff_mem (RingHom.ker (polynomialMap n).toRingHom)).mpr
    exact polynomialMap_H n)

@[simp] lemma toPolynomial_mk (n : ℕ) (v : P n) :
    toPolynomial n (mk n v) = polynomialMap n v := rfl

/-- The inverse polynomial presentation uses the forward matrix coordinates upstairs. -/
def fromPolynomial (n : ℕ) : R (4+n) →ₐ[ℂ] A n :=
  (mk n).comp ((matrixEquiv n).symm.toAlgHom.comp (includeHom n))

lemma toPolynomial_fromPolynomial (n : ℕ) :
    (toPolynomial n).comp (fromPolynomial n) = AlgHom.id ℂ (R (4+n)) := by
  apply AlgHom.ext
  intro r
  simp only [AlgHom.comp_apply, fromPolynomial, toPolynomial_mk, polynomialMap, AlgHom.id_apply]
  change eliminateHom n ((matrixEquiv n) ((matrixEquiv n).symm (includeHom n r))) = r
  rw [AlgEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (eliminateHom_includeHom n) r

lemma mk_matrix_symm_include_eliminate (n : ℕ) :
    ((mk n).comp (matrixEquiv n).symm.toAlgHom).comp
      ((includeHom n).comp (eliminateHom n)) =
    (mk n).comp (matrixEquiv n).symm.toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j
    · simp [AlgHom.comp_apply, eliminateHom, includeHom, p]
    · simp [AlgHom.comp_apply, eliminateHom, includeHom, s]
    · change mk n ((matrixEquiv n).symm (includeHom n (eliminateHom n (u n)))) =
        mk n ((matrixEquiv n).symm (u n))
      have hj : includeHom n (X ((3 : Fin 4).castAdd n)) = J n := by simp [includeHom]
      rw [eliminateHom_u, map_neg, hj]
      simp only [map_neg, matrixEquiv_symm_apply, changeHom_J, changeHom_u, map_one]
      rw [uChange_one]
      change -(mk n (J n)) = mk n (-H n - J n)
      simp
    · simp [AlgHom.comp_apply, eliminateHom, includeHom, F]
    · simp [AlgHom.comp_apply, eliminateHom, includeHom, J]
  · simp [AlgHom.comp_apply]

lemma fromPolynomial_toPolynomial (n : ℕ) :
    (fromPolynomial n).comp (toPolynomial n) = AlgHom.id ℂ (A n) := by
  apply Ideal.Quotient.algHom_ext ℂ
  apply AlgHom.ext
  intro v
  change fromPolynomial n (toPolynomial n (mk n v)) = mk n v
  rw [toPolynomial_mk]
  change mk n ((matrixEquiv n).symm (includeHom n
    (eliminateHom n ((matrixEquiv n) v)))) = mk n v
  have h := DFunLike.congr_fun (mk_matrix_symm_include_eliminate n) ((matrixEquiv n) v)
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using h

/-- Proposition 2.1, stable under adjoining any number of independent variables. -/
def polynomialPresentation (n : ℕ) : A n ≃ₐ[ℂ] R (4+n) :=
  AlgEquiv.ofAlgHom (toPolynomial n) (fromPolynomial n)
    (toPolynomial_fromPolynomial n) (fromPolynomial_toPolynomial n)

@[simp] lemma polynomialPresentation_mk (n : ℕ) (v : P n) :
    polynomialPresentation n (mk n v) = polynomialMap n v := rfl


/-- The distinguished source variable is exactly the polynomial in the question,
renamed into the first four variables; the extra variables are not involved. -/
lemma polynomialPresentation_p (n : ℕ) :
    polynomialPresentation n (mk n (p n)) =
      MvPolynomial.rename (Fin.castAdd n : Fin 4 → Fin (4+n)) StableCoordinate.f := by
  rw [polynomialPresentation_mk]
  simp [polynomialMap, pChange, quad, StableCoordinate.f, StableCoordinate.Q, map_ofNat]
  ring

@[simp] lemma polynomialPresentation_extra (n : ℕ) (i : Fin n) :
    polynomialPresentation n (mk n (X (i.natAdd 5))) = X (i.natAdd 4) := by
  simp [polynomialMap]

/-- The unstabilized polynomial presentation. -/
abbrev originalPresentation : A 0 ≃ₐ[ℂ] R 4 := polynomialPresentation 0

lemma originalPresentation_p : originalPresentation (mk 0 (p 0)) = StableCoordinate.f := by
  simpa using polynomialPresentation_p 0

/-- The same presentation after adjoining one independent variable. -/
abbrev stabilizedPresentation : A 1 ≃ₐ[ℂ] R 5 := polynomialPresentation 1

lemma stabilizedPresentation_p :
    stabilizedPresentation (mk 1 (p 1)) = stabilize StableCoordinate.f := by
  have hi : (Fin.castAdd 1 : Fin 4 → Fin 5) = Fin.castSucc := by
    funext i
    apply Fin.ext
    rfl
  simpa [stabilize, hi] using polynomialPresentation_p 1

end
end StableCoordinate.Presentation

end OAI
