import OAI.RepresentationTheory.RestrictedTilting.Basic

namespace OAI

namespace FiberFunctorProof
open scoped LaurentPolynomial BigOperators
universe u
variable (k : Type u) [Field k]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (SL2 k) (ι → k)) (hρ : IsRational k ρ)

noncomputable def rationalCoefficient (i j : ι) : MvPolynomial (Fin 2 × Fin 2) k :=
  (hρ (Pi.single j 1) (LinearMap.proj i)).choose

lemma eval_rationalCoefficient (g : SL2 k) (i j : ι) :
    MvPolynomial.eval (fun ij => g ij.1 ij.2) (rationalCoefficient k ρ hρ i j) =
      LinearMap.toMatrix' (ρ g) i j := by
  exact ((hρ (Pi.single j 1) (LinearMap.proj i)).choose_spec g).symm

noncomputable def unipotentPolynomialCoordinates (ij : Fin 2 × Fin 2) : Polynomial k :=
  if ij.1 = ij.2 then 1 else if ij = (0,1) then Polynomial.X else 0

noncomputable def torusLaurentCoordinates (ij : Fin 2 × Fin 2) : LaurentPolynomial k :=
  if ij = (0,0) then LaurentPolynomial.T 1 else
  if ij = (1,1) then LaurentPolynomial.T (-1) else 0

noncomputable def rationalUnipotentMatrix : Matrix ι ι (Polynomial k) := fun i j =>
  MvPolynomial.eval₂ Polynomial.C (unipotentPolynomialCoordinates k)
    (rationalCoefficient k ρ hρ i j)

noncomputable def rationalTorusMatrix : Matrix ι ι (LaurentPolynomial k) := fun i j =>
  MvPolynomial.eval₂ LaurentPolynomial.C (torusLaurentCoordinates k)
    (rationalCoefficient k ρ hρ i j)

lemma eval_unipotentPolynomialCoordinates (t : k) (ij : Fin 2 × Fin 2) :
    (unipotentPolynomialCoordinates k ij).eval t = unipotent k t ij.1 ij.2 := by
  obtain ⟨i,j⟩ := ij
  fin_cases i <;> fin_cases j <;> simp [unipotentPolynomialCoordinates, unipotent]

lemma eval_torusLaurentCoordinates (a : kˣ) (ij : Fin 2 × Fin 2) :
    LaurentPolynomial.eval₂ (RingHom.id k) a (torusLaurentCoordinates k ij) =
      diagonalTorus k a ij.1 ij.2 := by
  change _ = (!![(a : k), 0; 0, (↑a⁻¹ : k)] : Matrix (Fin 2) (Fin 2) k) ij.1 ij.2
  obtain ⟨i,j⟩ := ij
  fin_cases i <;> fin_cases j <;>
    simp [torusLaurentCoordinates, LaurentPolynomial.eval₂_T]

lemma eval_rationalUnipotentMatrix (t : k) :
    (rationalUnipotentMatrix k ρ hρ).map (Polynomial.evalRingHom t) =
      LinearMap.toMatrix' (ρ (unipotent k t)) := by
  ext i j
  change Polynomial.eval t (MvPolynomial.eval₂ _ _ _) = _
  have hcomp : (Polynomial.evalRingHom t).comp
      (MvPolynomial.eval₂Hom Polynomial.C (unipotentPolynomialCoordinates k)) =
      MvPolynomial.eval (fun ij => unipotent k t ij.1 ij.2) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro ij; simpa using eval_unipotentPolynomialCoordinates k t ij
  have he := congrArg (fun f : MvPolynomial (Fin 2 × Fin 2) k →+* k =>
    f (rationalCoefficient k ρ hρ i j)) hcomp
  exact he.trans (eval_rationalCoefficient k ρ hρ _ i j)

lemma eval_rationalTorusMatrix (a : kˣ) :
    (rationalTorusMatrix k ρ hρ).map (LaurentPolynomial.eval₂ (RingHom.id k) a) =
      LinearMap.toMatrix' (ρ (diagonalTorus k a)) := by
  ext i j
  change LaurentPolynomial.eval₂ (RingHom.id k) a (MvPolynomial.eval₂ _ _ _) = _
  have hcomp : (LaurentPolynomial.eval₂ (RingHom.id k) a).comp
      (MvPolynomial.eval₂Hom LaurentPolynomial.C (torusLaurentCoordinates k)) =
      MvPolynomial.eval (fun ij => diagonalTorus k a ij.1 ij.2) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [LaurentPolynomial.eval₂_C]
    · intro ij; simpa using eval_torusLaurentCoordinates k a ij
  have he := congrArg (fun f : MvPolynomial (Fin 2 × Fin 2) k →+* k =>
    f (rationalCoefficient k ρ hρ i j)) hcomp
  exact he.trans (eval_rationalCoefficient k ρ hρ _ i j)
end FiberFunctorProof

end OAI
