import OAI.Analysis.KadisonKastler.RelativePowersStormer
import OAI.Analysis.KadisonKastler.UnitaryStateDefect

namespace OAI

/-! # State commutator bounds in a finite-matrix relative commutant

The relative Powers–Størmer estimate supplies the unitary defect bound
on the central-vector space, without treating the relative algebra as
cyclic on the full ambient Hilbert space.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance relativeUnitaryStateRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

omit [Nonempty ι] in
theorem relative_conjugation_mem_commutant (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (a : Algebra E.relativeVonNeumann) :
    conjugationOperator J a.val ∈ E.relativeVonNeumann.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  exact VonNeumannAlgebra.mem_commutant_iff.mp
    (hright ⟨a.val,E.relativeVonNeumann_le a.property⟩) T (E.relativeVonNeumann_le hT)

omit [Nonempty ι] in
theorem relative_modularQuadratic_mem_central (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (a : Algebra E.relativeVonNeumann) {η : H}
    (hη : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J) :
    modularQuadratic J a η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J := by
  apply relative_algebra_orbit_mem_central E J hright _ ?_ a
  apply centralVectorSpace_conjugate _ J hJ
  apply relative_algebra_orbit_mem_central E J hright _ ?_ a
  exact centralVectorSpace_conjugate _ J hJ hη

theorem relative_centralVectorDefect_unitary_sq_le_stateCommutator
    (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hηE : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (u : unitary (Algebra E.relativeVonNeumann)) :
    ‖centralVectorDefect J η u.val.val‖^2 ≤ ‖vectorStateCommutator η u.val‖ := by
  let a : Algebra M := ⟨(star u).val.val,E.relativeVonNeumann_le (star u).val.property⟩
  have hcone : modularQuadratic J (star u).val η ∈ modularPositiveCone (M := M) J ξ :=
    modularQuadratic_preserves_positiveCone J hJ hright ξ a hη
  have hcentral := relative_modularQuadratic_mem_central E J hJ hright (star u).val hηE
  have hs := relative_positiveCone_norm_sq_le_state_norm E J hJ hright hleft ξ hξ hcyc hpos
    hcone hη hcentral hηE
  rw [← modularUnitary_coe J hJ (star u),modularUnitary_vectorFunctional J hJ
    (relative_conjugation_mem_commutant E J hright)] at hs
  rw [centralVectorDefect_unitary_norm_eq J hJ η u]
  exact hs.trans (sandwich_unitary_state_norm_sub_le η u)

end

end KadisonKastler

end OAI
