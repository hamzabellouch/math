import OAI.Analysis.KadisonKastler.PrescribedMatrixState
import OAI.Analysis.KadisonKastler.CornerStateConjugation
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI

/-! # Transporting positive matrix-central vectors by inner automorphisms

The modular quadratic unitary transports the concrete matrix algebra,
its positive central vector and the associated vector state together.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

def modularUnitary (u : unitary (Algebra M)) : unitary (H →L[ℂ] H) :=
  ambientAlgebraUnitary u * conjugationUnitary J hJ (ambientAlgebraUnitary u)

theorem modularUnitary_coe (u : unitary (Algebra M)) :
    (modularUnitary J hJ u : H →L[ℂ] H) = modularQuadratic J u.val := rfl

include hJ hright in
theorem conjugation_modularUnitary (u : unitary (Algebra M)) :
    conjugationOperator J (modularUnitary J hJ u) = modularUnitary J hJ u := by
  change conjugationOperator J (u.val.val*conjugationOperator J u.val.val) = _
  rw [conjugationOperator_mul J hJ,conjugationOperator_twice J hJ]
  exact (VonNeumannAlgebra.mem_commutant_iff.mp (hright u.val) u.val.val u.val.property).symm

include hright in
theorem modularUnitary_intertwines (u : unitary (Algebra M)) (a : Algebra M) :
    (u.val*a*star u.val).val * modularUnitary J hJ u =
      (modularUnitary J hJ u : H →L[ℂ] H)*a.val := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright u.val) a.val a.property
  change (u.val.val*a.val*star u.val.val)*(u.val.val*conjugationOperator J u.val.val) =
    (u.val.val*conjugationOperator J u.val.val)*a.val
  calc
    _ = u.val.val*a.val*(star u.val.val*u.val.val)*conjugationOperator J u.val.val := by
      simp only [mul_assoc]
    _ = u.val.val*a.val*conjugationOperator J u.val.val := by
      have hu : star u.val.val*u.val.val = 1 :=
        congrArg (fun a : Algebra M => a.val) u.property.1
      rw [hu,mul_one]
    _ = _ := by rw [mul_assoc,hc,mul_assoc]

include hJ hright in
theorem modularUnitary_right_intertwines (u : unitary (Algebra M)) (a : Algebra M) :
    conjugationOperator J (star (u.val*a*star u.val)).val * modularUnitary J hJ u =
      (modularUnitary J hJ u : H →L[ℂ] H)*conjugationOperator J (star a).val := by
  have he := congrArg (conjugationOperator J)
    (modularUnitary_intertwines J hJ hright u (star a))
  simp only [conjugationOperator_mul J hJ,conjugation_modularUnitary J hJ hright] at he
  simpa only [star_mul,star_star,StarMemClass.coe_star,mul_assoc] using he

include hJ hright in
theorem modularUnitary_vectorFunctional (u : unitary (Algebra M)) (η : H) :
    Generator.Tracial.vectorFunctional (M := M) ((modularUnitary J hJ u : H →L[ℂ] H) η) =
      sandwichFunctional (Generator.Tracial.vectorFunctional η) u.val := by
  let U := ambientAlgebraUnitary u
  let V := conjugationUnitary J hJ U
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright u.val) U u.val.property
  have he : (modularUnitary J hJ u : H →L[ℂ] H) η =
      (V : H →L[ℂ] H) ((U : H →L[ℂ] H) η) :=
    congrArg (fun T : H →L[ℂ] H => T η) hc
  rw [he,vectorFunctional_commuting_unitary (M := M) _ V (hright u.val),
    sandwichFunctional_vectorFunctional]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def unitaryConjugateMatrixUnits (E : MatrixUnitSystem ι (Algebra M))
    (u : unitary (Algebra M)) : MatrixUnitSystem ι (Algebra M) :=
  E.map (Unitary.conjStarAlgAut ℂ (Algebra M) u).toStarAlgHom

include hJ hright in
theorem modularUnitary_matrix_central (E : MatrixUnitSystem ι (Algebra M))
    (u : unitary (Algebra M)) {η : H}
    (hη : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J) :
    (modularUnitary J hJ u : H →L[ℂ] H) η ∈
      centralVectorSpace (matrixUnitConcreteAlgebra (unitaryConjugateMatrixUnits E u)) J := by
  apply (mem_centralVectorSpace_matrix_iff _ J _).mpr
  intro i j
  have h := (mem_centralVectorSpace_matrix_iff E J η).mp hη i j
  change (u.val*E.entry i j*star u.val).val ((modularUnitary J hJ u : H →L[ℂ] H) η) =
    conjugationOperator J (star (u.val*E.entry i j*star u.val)).val
      ((modularUnitary J hJ u : H →L[ℂ] H) η)
  change ((u.val*E.entry i j*star u.val).val*modularUnitary J hJ u) η =
    (conjugationOperator J (star (u.val*E.entry i j*star u.val)).val*modularUnitary J hJ u) η
  rw [modularUnitary_intertwines J hJ hright,modularUnitary_right_intertwines J hJ hright]
  change (modularUnitary J hJ u : H →L[ℂ] H) ((E.entry i j).val η) =
    (modularUnitary J hJ u : H →L[ℂ] H) (conjugationOperator J (star (E.entry i j)).val η)
  simpa only [StarMemClass.coe_star] using
    congrArg (modularUnitary J hJ u : H →L[ℂ] H) h

end

end KadisonKastler

end OAI
