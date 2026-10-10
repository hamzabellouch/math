import OAI.Analysis.KadisonSimilarity.Tracial.PredualGNSSeparable
import OAI.Analysis.KadisonSimilarity.Tracial.NormalTracialGeometry
import OAI.Analysis.FactorGeneration.MatrixSequence

namespace OAI

/-! Irreducible increasing matrix subfactors in the normal tracial GNS
representation. The matrix refinement theorem is applied after deriving
separability of that representation from the given predual. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

private theorem scalar_center_of_starEquiv {A B : Type*}
    [Ring A] [StarRing A] [Algebra ℂ A] [Ring B] [StarRing B] [Algebra ℂ B]
    (e : A ≃⋆ₐ[ℂ] B)
    (h : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • (1 : A)) :
    ∀ c : B, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • (1 : B) := by
  intro c hc
  obtain ⟨b, rfl⟩ := e.surjective c
  change ∀ a : B, a * e b = e b * a at hc
  have hb (a : A) : a * b = b * a := by
    apply e.injective
    change e (a * b) = e (b * a)
    rw [map_mul e a b, map_mul e b a]
    exact hc (e a)
  obtain ⟨z, hz⟩ := h b hb
  refine ⟨z, ?_⟩
  change e b = z • (1 : B)
  rw [hz, map_smul, map_one]

private theorem diffuse_projections_of_starEquiv {A B : Type*}
    [Ring A] [StarRing A] [Algebra ℂ A] [Ring B] [StarRing B] [Algebra ℂ B]
    (e : A ≃⋆ₐ[ℂ] B)
    (h : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q) :
    ∀ p : B, IsStarProjection p → p ≠ 0 →
      ∃ q : B, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
  intro p hp hp0
  obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ := h (e.symm p) (hp.map e.symm)
    (fun hz => hp0 (by simpa only [map_zero, e.apply_symm_apply] using congrArg e hz))
  refine ⟨e q, hq.map e, ?_, ?_, ?_, ?_⟩
  · intro hz
    apply hq0
    apply e.injective
    change e q = e 0
    simpa only [map_zero] using hz
  · exact fun hz => hqp (by simpa only [e.symm_apply_apply] using congrArg e.symm hz)
  · simpa only [map_mul, e.apply_symm_apply] using congrArg e hpq
  · simpa only [map_mul, e.apply_symm_apply] using congrArg e hqp'

universe u
variable {A X : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (τ : A →ₚ[ℂ] ℂ)

/-- The irreducible hyperfinite presentation is constructed in the faithful
normal GNS representation of a diffuse finite factor. -/
theorem exists_gns_irreducible_matrix_subfactor
    (h1 : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hf : ∀ a, τ (star a * a) = 0 → a = 0)
    (hnormal : BoundedHochschild.TraceInPredual e τ)
    (hfactor : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • (1 : A))
    (hdiff : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q) :
    let N := representationVonNeumannAlgebra τ.gnsStarAlgHom
    ∃ F : ℕ → FiniteMatrixStage N,
      F 0 = FiniteMatrixStage.scalarStage N ∧
      Monotone (fun n => (F n).units.concreteAlgebra) ∧
      (∀ n, FiniteDimensional ℂ (F n).units.concreteAlgebra) ∧
      IsII1Factor (FiniteMatrixStage.generated F) ∧
      FiniteMatrixStage.generated F ≤ N.toStarSubalgebra ∧
      ∀ c : N.toStarSubalgebra,
        (∀ a : FiniteMatrixStage.generated F, a.val * c.val = c.val * a.val) →
        ∃ z : ℂ, c = z • (1 : N.toStarSubalgebra) := by
  let N := representationVonNeumannAlgebra τ.gnsStarAlgHom
  let G := gnsTracialGeometry τ htr
  have hN : G.left.range = N.toStarSubalgebra := hasNormalGNS_of_predual e τ hnormal htr
  let υ := G.normalTracialRepresentation h1 (gnsTracialVector_injective τ hf) N hN
  let f := equivalenceOfConcreteRange N G.left
    (G.left_injective (gnsTracialVector_injective τ hf)) hN
  let := gns_separable_of_predual e τ hnormal
  have hcenter := scalar_center_of_starEquiv f hfactor
  have hdiffN := diffuse_projections_of_starEquiv f hdiff
  obtain ⟨F, hF0, hmono, hfd, hII, hFN, hirr⟩ :=
    FiniteMatrixStage.exists_irreducible_matrix_generated_II1 υ le_rfl hcenter hdiffN
      (fun c hc => hcenter c (fun a => by
        have h := hc a
        change a * c = c * a at h
        exact h))
      (TopologicalSpace.IsSeparable.of_separableSpace _)
  exact ⟨F, hF0, hmono, hfd, hII, hFN, fun c hc => ⟨υ.trace c, hirr c hc⟩⟩

end KadisonSimilarity

end

end OAI
