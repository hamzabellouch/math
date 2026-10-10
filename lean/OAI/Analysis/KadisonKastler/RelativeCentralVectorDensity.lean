import OAI.Analysis.KadisonKastler.MatrixCentralProjection
import OAI.Analysis.KadisonKastler.PositiveMatrixAveraging

namespace OAI

/-! # The relative commutant is cyclic on the central-vector space

Compressing an algebra orbit by the finite central-vector projection is
exactly the matrix relative-commutant average. Density on the original
space therefore gives density on the central-vector space.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (E : MatrixUnitSystem ι (Algebra M))

/-- The actual algebra element obtained by finite matrix averaging. -/
def matrixRelativeAverage (a : Algebra M) : Algebra E.relativeVonNeumann :=
  E.relativeEquiv ((Fintype.card ι : ℂ)⁻¹ • ∑ j,
    (⟨E.amplify j a,E.amplify_mem j a⟩ : E.commutant))

omit [Nonempty ι] in
theorem matrixRelativeAverage_apply (a : Algebra M) (η : H) :
    (matrixRelativeAverage E a).val η = (Fintype.card ι : ℂ)⁻¹ •
      ∑ j, ∑ i, (E.entry i j).val (a.val ((E.entry j i).val η)) := by
  change ((Fintype.card ι : ℂ)⁻¹ • M.toStarSubalgebra.subtype
    (E.commutant.subtype (∑ j,
      (⟨E.amplify j a,E.amplify_mem j a⟩ : E.commutant)))) η = _
  rw [map_sum E.commutant.subtype,map_sum M.toStarSubalgebra.subtype]
  change ((Fintype.card ι : ℂ)⁻¹ • (∑ j, (E.amplify j a).val)) η = _
  simp only [smul_apply,sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change M.toStarSubalgebra.subtype (∑ i, E.entry i j * a * E.entry j i) η = _
  rw [map_sum M.toStarSubalgebra.subtype]
  simp only [sum_apply,map_mul,mul_apply_eq_comp]
  rfl

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ hright in
theorem matrixCentralProjection_algebraVector (η : H)
    (hη : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J) (a : Algebra M) :
    (centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection (a.val η) =
      (matrixRelativeAverage E a).val η := by
  rw [matrixCentralProjection_eq E J hJ hright,matrixRelativeAverage_apply]
  change (Fintype.card ι : ℂ)⁻¹ •
    ((∑ i, ∑ j, (E.entry i j).val * conjugationOperator J (E.entry i j).val) (a.val η)) = _
  simp only [sum_apply]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have hc := congrArg (fun T : H →L[ℂ] H => T η)
    (VonNeumannAlgebra.mem_commutant_iff.mp (hright (E.entry i j)) a.val a.property)
  have hv := (mem_centralVectorSpace_matrix_iff E J η).mp hη j i
  have hs : (star (E.entry j i)).val = (E.entry i j).val :=
    congrArg Subtype.val (E.star_entry j i)
  change (E.entry j i).val η = conjugationOperator J (star (E.entry j i)).val η at hv
  rw [hs] at hv
  change (E.entry i j).val (conjugationOperator J (E.entry i j).val (a.val η)) = _
  change a.val (conjugationOperator J (E.entry i j).val η) =
    conjugationOperator J (E.entry i j).val (a.val η) at hc
  rw [← hc,← hv]

include hright in
omit [Nonempty ι] in
theorem relative_algebra_orbit_mem_central (η : H)
    (hη : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (a : Algebra E.relativeVonNeumann) :
    a.val η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J := by
  have ha := (E.relativeStar_mem a.val).mp a.property
  apply (mem_centralVectorSpace_matrix_iff E J _).mpr
  intro i j
  have he := congrArg (fun T : H →L[ℂ] H => T η) (ha.2 i j)
  have hv := (mem_centralVectorSpace_matrix_iff E J η).mp hη i j
  have hc := congrArg (fun T : H →L[ℂ] H => T η)
    (VonNeumannAlgebra.mem_commutant_iff.mp (hright (star (E.entry i j))) a.val ha.1)
  change (E.entry i j).val (a.val η) = a.val ((E.entry i j).val η) at he
  change a.val (conjugationOperator J (star (E.entry i j)).val η) =
    conjugationOperator J (star (E.entry i j)).val (a.val η) at hc
  exact he.trans ((congrArg a.val hv).trans hc)

include hJ hright in
theorem relative_centralVector_orbit_dense (η : H)
    (hη : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (hcyc : DenseRange (algebraVectorMap M η)) :
    closure (Set.range (fun a : Algebra E.relativeVonNeumann => a.val η)) =
      (centralVectorSpace (matrixUnitConcreteAlgebra E) J : Set H) := by
  let K := centralVectorSpace (matrixUnitConcreteAlgebra E) J
  let S := Set.range (fun a : Algebra E.relativeVonNeumann => a.val η)
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro _ ⟨a,rfl⟩
      exact relative_algebra_orbit_mem_central E J hright η hη a
    · exact centralVectorSpace_isClosed _ J
  · intro x hx
    have hall (v : H) : K.starProjection v ∈ closure S := by
      apply hcyc.induction_on (p := fun v => K.starProjection v ∈ closure S) v
      · exact isClosed_closure.preimage K.starProjection.continuous
      · intro a
        change (centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection (a.val η) ∈ closure S
        rw [matrixCentralProjection_algebraVector E J hJ hright η hη a]
        exact subset_closure ⟨matrixRelativeAverage E a,rfl⟩
    have he : K.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    simpa only [he] using hall x

end

end KadisonKastler

end OAI
