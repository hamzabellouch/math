import OAI.Analysis.KadisonSimilarity.Representation.ProjectionComparisonTransport
import OAI.Analysis.KadisonSimilarity.Tracial.NormalTracialGeometry
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixCenter
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixGNSNormality
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixRelativeCommutant

namespace OAI

/-! Projection comparison in the finite-matrix source follows from its
actual normal trace and dense full-matrix tower. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped CStarAlgebra ComplexOrder

namespace TracialCornerGeometry
variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

local instance normalFactor_closed (N : VonNeumannAlgebra H) :
    IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed N

theorem projectionComparison_of_normal_range (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (N : VonNeumannAlgebra H)
    (hN : G.left.range = N.toStarSubalgebra)
    (hfactor : ∀ c : P, (∀ a : P, a * c = c * a) → ∃ z : ℂ, c = z • (1 : P)) :
    FiniteFactorProjectionComparison (fun a => (G.trace a).re) := by
  let τ := G.normalTracialRepresentation h1 hf N hN
  let e := equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  have hfactorN : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra, a * c = c * a) →
        ∃ z : ℂ, c = z • (1 : N.toStarSubalgebra) := by
    intro c hc
    obtain ⟨b, rfl⟩ := e.surjective c
    change ∀ a : N.toStarSubalgebra, a * e b = e b * a at hc
    have hb (a : P) : a * b = b * a := by
      apply e.injective
      change e (a * b) = e (b * a)
      rw [map_mul e a b, map_mul e b a]
      exact hc (e a)
    obtain ⟨z, hz⟩ := hfactor b hb
    refine ⟨z, ?_⟩
    change e b = z • (1 : N.toStarSubalgebra)
    rw [hz, map_smul, map_one]
  exact finiteFactorProjectionComparison_of_equiv e
    (fun a => (G.trace a).re) (fun a => (τ.trace a).re)
    (fun a => congrArg Complex.re (G.normalTracialRepresentation_trace h1 hf N hN a))
    (finiteFactorProjectionComparison τ hfactorN)

end TracialCornerGeometry

variable {R : Type*} [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  (τ : R →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
  (hf : ∀ a, τ (star a * a) = 0 → a = 0)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τ.toLinearMap (gnsTracialVector τ))
  (hnormal : τ.gnsStarAlgHom.range =
    (representationVonNeumannAlgebra τ.gnsStarAlgHom).toStarSubalgebra)

include h1 htr hf M hnormal in
/-- The comparison input for every matrix size in the actual source model. -/
theorem matrix_projectionComparison_of_tower (n : ℕ) [NeZero n] :
    FiniteFactorProjectionComparison
      (fun X : CStarMatrix (Fin n) (Fin n) R => (normalizedMatrixTrace τ n X).re) := by
  let G := gnsTracialGeometry τ htr
  have hcenter : ∀ c : R, (∀ a : R, c * a = a * c) →
      ∃ z : ℂ, c = algebraMap ℂ R z := by
    intro c hc
    obtain ⟨z, hz⟩ := G.scalar_center_of_matrix_tower M (gnsTracialVector_injective τ hf)
      c (fun a => (hc a).symm)
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  have hid (X : CStarMatrix (Fin n) (Fin n) R) :
      matrixEntryHom (StarAlgHom.id ℂ R) X = X := by
    ext i j
    rfl
  have hcenterN : ∀ X : CStarMatrix (Fin n) (Fin n) R,
      (∀ Y, Y * X = X * Y) → ∃ z : ℂ, X = z • (1 : CStarMatrix (Fin n) (Fin n) R) := by
    intro X hX
    obtain ⟨z, hz⟩ := scalar_of_matrix_relative_commutant (StarAlgHom.id ℂ R)
      hcenter X (fun Y => by rw [hid]; exact (hX Y).symm)
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  let Gn := gnsTracialGeometry (normalizedMatrixTrace τ n) (normalizedMatrixTrace_tracial τ htr)
  exact Gn.projectionComparison_of_normal_range (normalizedMatrixTrace_one τ h1)
      (gnsTracialVector_injective _ (normalizedMatrixTrace_faithful τ hf)) _
      (matrix_gns_normal_range τ _ hnormal n) hcenterN

end KadisonSimilarity

end

end OAI
