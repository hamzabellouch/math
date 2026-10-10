import OAI.Analysis.KadisonKastler.PositiveUnitaryTransport
import OAI.Analysis.KadisonKastler.NormalizedPositivePinching

namespace OAI

/-! # Projection centrality and faithfulness under positive unitary transport -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem vectorFunctional_centralizes_projection
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (p : AlgebraProjection M) (η : H)
    (hcentral : p.val.val η=conjugationOperator J p.val.val η) :
    ∀ x : Algebra M, vectorFunctional η (p.val*x)=vectorFunctional η (x*p.val) := by
  have hp : star p.val.val=p.val.val :=
    (p.property.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
  have hs : star (conjugationOperator J p.val.val)=conjugationOperator J p.val.val := by
    rw [← conjugationOperator_star J hJ,hp]
  intro x
  exact vector_functional_commutes_of_right_vector M η p.val.val
    (conjugationOperator J p.val.val) (hright p.val) hcentral
    (by rw [hp,hs]; exact hcentral) x

theorem matrixCentralVector_projection_state
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (η : H) (hη : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (p : AlgebraProjection M) (hp : p.val ∈ E.algebra) :
    ∀ x : Algebra M, vectorFunctional η (p.val*x)=vectorFunctional η (x*p.val) := by
  have hm : p.val.val ∈ matrixUnitConcreteAlgebra E := (E.mem_concreteAlgebra p.val).mpr hp
  have hc := hη (⟨p.val.val,hm⟩ : Algebra (matrixUnitConcreteAlgebra E))
  have hstar : star p.val.val=p.val.val :=
    (p.property.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
  change p.val.val η=conjugationOperator J (star p.val.val) η at hc
  rw [hstar] at hc
  exact vectorFunctional_centralizes_projection J hJ hright p η hc

theorem algebraUnitary_vector_separating (u : unitary (Algebra M)) (η : H)
    (hη : Function.Injective (algebraVectorMap M η)) :
    Function.Injective (algebraVectorMap M (u.val.val η)) := by
  intro a b hab
  have he : a*u.val=b*u.val := hη hab
  have hh := congrArg (fun x : Algebra M => x*star u.val) he
  simpa only [mul_assoc,u.property.2,mul_one] using hh

theorem commutantUnitary_vector_separating (u : unitary (H →L[ℂ] H))
    (hu : (u : H →L[ℂ] H) ∈ M.commutant) (η : H)
    (hη : Function.Injective (algebraVectorMap M η)) :
    Function.Injective (algebraVectorMap M ((u : H →L[ℂ] H) η)) := by
  intro a b hab
  apply hη
  apply (Unitary.linearIsometryEquiv u).injective
  have ha := congrArg (fun T : H →L[ℂ] H => T η)
    (VonNeumannAlgebra.mem_commutant_iff.mp hu a.val a.property)
  have hb := congrArg (fun T : H →L[ℂ] H => T η)
    (VonNeumannAlgebra.mem_commutant_iff.mp hu b.val b.property)
  exact ha.symm.trans (hab.trans hb)

theorem modularUnitary_vector_separating
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (u : unitary (Algebra M)) (η : H)
    (hη : Function.Injective (algebraVectorMap M η)) :
    Function.Injective (algebraVectorMap M ((modularUnitary J hJ u : H →L[ℂ] H) η)) := by
  let U := ambientAlgebraUnitary u
  let V := conjugationUnitary J hJ U
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright u.val) U u.val.property
  have he : (modularUnitary J hJ u : H →L[ℂ] H) η=(V : H →L[ℂ] H) (u.val.val η) :=
    congrArg (fun T : H →L[ℂ] H => T η) hc
  rw [he]
  exact commutantUnitary_vector_separating V (hright u.val) _
    (algebraUnitary_vector_separating u η hη)

end

end KadisonKastler

end OAI
