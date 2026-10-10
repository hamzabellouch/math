import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectPolynomialCurves
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectAxisExponential
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateMatrixRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentMatrixSpanning

namespace OAI

/-! # Faithful unipotent representation of the semidirect model

Only the smaller ideal has polynomial exponential coordinates. For the new
model, polynomial coordinate translates and the two factor subgroups suffice.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

include b in
theorem semidirectMatrixProducts
    (hnil : letI := derivationSemidirectGroup D hD
      letI := derivationSemidirectLieGroup D hD
      LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ))) :
    letI := derivationSemidirectGroup D hD
    letI := derivationSemidirectLieGroup D hD
    ∀ {m : ℕ} (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (semidirectCoordinate b)),
    ∃ c : ℕ, ∀ l : List (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)),
      c ≤ l.length →
        (l.map (coordinateMatrixDifferential (semidirectCoordinate b) B
          (contDiff_semidirectCoordinate b))).prod = 0 := by
  let := derivationSemidirectGroup D hD
  let _ : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  let _ : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let _ : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  let := derivationSemidirectLieGroup D hD
  intro m B
  let T := GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)
  let _ : LieRing.IsNilpotent T := hnil
  let q := semidirectCoordinate b
  have hq : ∀ i, ContDiff ℝ ∞ (q i) := contDiff_semidirectCoordinate b
  let j := coordinateMatrixDifferential q B hq
  let S : Set T := Set.range (fun x : L => ((x, 0) : T)) ∪ {((0, 1) : T)}
  have hS : Submodule.span ℝ S = ⊤ := by
    apply top_unique
    intro v _
    let p : L × ℝ := v
    have hleft : ((p.1, 0) : T) ∈ Submodule.span ℝ S :=
      Submodule.subset_span (Or.inl ⟨p.1, rfl⟩)
    have hright : ((0, 1) : T) ∈ Submodule.span ℝ S :=
      Submodule.subset_span (Or.inr (Set.mem_singleton _))
    have hsum := (Submodule.span ℝ S).add_mem hleft
      ((Submodule.span ℝ S).smul_mem p.2 hright)
    convert hsum using 1
    change p = ((p.1, 0) : L × ℝ) + p.2 • ((0, 1) : L × ℝ)
    ext <;> simp
  have hj (v : T) (hv : v ∈ S) : IsNilpotent (j v) := by
    rcases hv with ⟨x, rfl⟩ | hv
    · apply coordinateMatrixDifferential_nilpotent q B hq
      intro a z i
      have he (t : ℝ) : groupExponential (t • ((x, 0) : T)) =
          t • ((x, 0) : L × ℝ) := by
        exact (semidirect_exp_left_axis D hD x t).trans (by simp)
      have heq : (fun t : ℝ => q i (a * groupExponential (t • ((x, 0) : T)) * z)) =
          (fun t : ℝ => q i (a * (t • ((x, 0) : L × ℝ)) * z)) :=
        funext fun t => congrArg (fun p : L × ℝ => q i (a * p * z)) (he t)
      exact heq.symm ▸ semidirect_translated_line_polynomial b D hD a (x, 0) z i
    · obtain rfl := Set.mem_singleton_iff.mp hv
      apply coordinateMatrixDifferential_nilpotent q B hq
      intro a z i
      have he (t : ℝ) : groupExponential (t • ((0, 1) : T)) =
          t • ((0, 1) : L × ℝ) := by
        exact (semidirect_exp_right_axis D hD t).trans (by simp)
      have heq : (fun t : ℝ => q i (a * groupExponential (t • ((0, 1) : T)) * z)) =
          (fun t : ℝ => q i (a * (t • ((0, 1) : L × ℝ)) * z)) :=
        funext fun t => congrArg (fun p : L × ℝ => q i (a * p * z)) (he t)
      exact heq.symm ▸ semidirect_translated_line_polynomial b D hD a (0, 1) z i
  obtain ⟨c, hc⟩ := matrix_products_vanish_of_spanning_nilpotents j S hS hj
  exact ⟨c, hc⟩

include b in
theorem exists_semidirect_unipotent_representation
    (hnil : letI := derivationSemidirectGroup D hD
      letI := derivationSemidirectLieGroup D hD
      LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ))) :
    letI := derivationSemidirectGroup D hD
    letI : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
    letI : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
    letI := derivationSemidirectLieGroup D hD
    ∃ (m c : ℕ) (ρ : (L × ℝ) →* Matrix.GeneralLinearGroup (Fin m) ℝ)
      (j : GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ) →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ),
      Function.Injective ρ ∧ Function.Injective j ∧
      @HasMFDerivAt ℝ _ (L × ℝ) _ _ (L × ℝ) _ (𝓘(ℝ, L × ℝ))
        (L × ℝ) _ _ (Matrix (Fin m) (Fin m) ℝ) _ _
        (Matrix (Fin m) (Fin m) ℝ) _ (𝓘(ℝ, Matrix (Fin m) (Fin m) ℝ))
        (Matrix (Fin m) (Fin m) ℝ) _ (chartedSpaceSelf _)
        (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) 1 j.toLinearMap.toContinuousLinearMap ∧
      (∀ l : List (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)),
        c ≤ l.length → (l.map j).prod = 0) := by
  let := derivationSemidirectGroup D hD
  let _ : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  let _ : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let _ : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  let := derivationSemidirectLieGroup D hD
  let T := GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)
  let _ : LieRing.IsNilpotent T := hnil
  let q := semidirectCoordinate b
  let := finiteDimensional_semidirectCoordinateOrbit b D hD
  let m := Module.finrank ℝ (coordinateOrbitSpan q)
  let B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan q :=
    (Module.finBasis ℝ (coordinateOrbitSpan q)).equivFun.symm
  have hq : ∀ i, ContDiff ℝ ∞ (q i) := contDiff_semidirectCoordinate b
  let ρ := coordinateMatrixRepresentation q B
  let j := coordinateMatrixDifferential q B hq
  obtain ⟨c, hc⟩ := semidirectMatrixProducts b D hD hnil B
  exact ⟨m, c, ρ, j,
    coordinateMatrixRepresentation_injective q B (semidirectCoordinate_injective b),
    coordinateMatrixDifferential_injective q B hq (semidirectCoordinate_injective b),
    hasMFDerivAt_unitsHomLieDifferential ρ (contDiff_coordinateMatrixRepresentation q B hq).contMDiff,
    hc⟩

end PolycyclicRecognition

end

end OAI
