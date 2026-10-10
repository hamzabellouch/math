import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentIntrinsicIntegration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConstructedNilpotentPublishedInputs

namespace OAI

/-! # Integrating a given nilpotent model into any Lie group

The now-proved nilpotent-model comparison transports the source to the
constructed coordinate model. Intrinsic integration then reaches the target.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

theorem nilpotentSmoothIntegrationInput
    (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (N : NilpotentLieModel L) :
    NilpotentSmoothIntegrationInput (EN := N.modelSpace) (N := N.carrier) (EG := E) (G := G) := by
  intro _ hn f
  let b := Module.finBasis ℝ L
  let : NormedAddCommGroup L := NormedAddCommGroup.induced L _ b.equivFun b.equivFun.injective
  let : NormedSpace ℝ L := NormedSpace.induced ℝ L _ b.equivFun
  let : RealNormedLieAlgebra L :=
    { (inferInstance : NormedAddCommGroup L), (inferInstance : LieRing L),
      (inferInstance : NormedSpace ℝ L), (inferInstance : LieAlgebra ℝ L) with }
  have hL : LieRing.IsNilpotent L := N.equiv.nilpotent_iff_equiv_nilpotent.mpr hn
  let : LieRing.IsNilpotent L := hL
  obtain ⟨P⟩ := polynomialExponentialCoordinates_nilpotent L hL
  let := P
  let : Group L := P.group
  let Q := polynomialCoordinateLieModel L
  let fL := f.comp N.equiv.toLieHom
  obtain ⟨φ, hφ, hφexp⟩ := integrate_polynomial_nilpotent
    groupExponential groupExponential_isGroupExponential L hL fL
  obtain ⟨η, hη, _, hηexp⟩ := nilpotentPublishedInputs.integrate L L N Q inferInstance hn
    (Q.equiv.toLieHom.comp N.equiv.symm.toLieHom) groupExponential
    (fun x : GroupLieAlgebra (𝓘(ℝ, L)) L => (x : L))
    groupExponential_isGroupExponential
    (PolynomialExponentialCoordinates.isGroupExponential_identity (L := L) (P := P))
  change N.carrier →* L at η
  change ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, L)) ∞ η at hη
  change ∀ v : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier,
    η (groupExponential v) = P.tangentEquiv (N.equiv.symm v) at hηexp
  let χ : N.carrier →* G := φ.comp η
  have hχ := hφ.comp hη
  have hχexp (v : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :
      χ (groupExponential v) = groupExponential (f v) := by
    change φ (η (groupExponential v)) = _
    rw [hηexp]
    rw [P.tangentEquiv_apply, hφexp]
    change groupExponential (f (N.equiv (N.equiv.symm v))) = _
    rw [N.equiv.apply_symm_apply]
  exact ⟨χ, hχ, mfderiv_eq_of_exponential_compatibility
    groupExponential_isGroupExponential groupExponential_isGroupExponential
    χ (hχ.mdifferentiable (by simp)) f.toLinearMap hχexp⟩

end PolycyclicRecognition

end

end OAI
