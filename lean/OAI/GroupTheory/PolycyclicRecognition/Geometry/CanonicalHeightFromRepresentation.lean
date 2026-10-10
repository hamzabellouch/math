import OAI.GroupTheory.PolycyclicRecognition.Geometry.AdjointMatrixHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalHeightIntegration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput

namespace OAI

/-! # Constructing canonical height directly from the adjoint diagonal

The scalar-character integration input is unnecessary for this application:
the logarithmic diagonal of the actual adjoint representation already
integrates every canonical height character. Continuity is obtained from
the global exponential chart, separately from this algebraic construction.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

section Topological

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

theorem exists_canonical_height_of_representation
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (e : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (he : ∀ x, e x = Exp x)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ) (hρExp : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) :
    ∃ π : G →* Multiplicative W,
      Continuous (fun g => (π g).toAdd) ∧
      (∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) ∧
      Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) := by
  have hsurj : Function.Surjective Exp := by
    intro g
    obtain ⟨x, hx⟩ := e.surjective g
    exact ⟨x, (he x).symm.trans hx⟩
  let c := adjointCharacterHom T hExp hsurj j ρ hρ hρExp
  have hcExp (x) (i : Fin a) : (c (Exp x)).toAdd i = T.character i x :=
    adjointCharacterHom_exp T hExp hsurj j ρ hρ hρExp x i
  have hc (i : Fin a) (g : G) : T.character i (e.symm g) = (c g).toAdd i := by
    rw [← hcExp, ← he, e.apply_symm_apply]
  have hzero : heightProjection T.character (e.symm 1) = 0 := by
    apply heightCharacters_separate T.character
    intro i
    rw [heightCharacter_projection, hc, map_one]
    rfl
  have hmul (g h : G) : heightProjection T.character (e.symm (g * h)) =
      heightProjection T.character (e.symm g) + heightProjection T.character (e.symm h) := by
    apply sub_eq_zero.mp
    apply heightCharacters_separate T.character
    intro i
    simp only [map_sub, map_add, heightCharacter_projection, hc, map_mul, toAdd_mul,
      Pi.add_apply]
    abel
  let π : G →* Multiplicative W :=
    { toFun := fun g => Multiplicative.ofAdd (q (heightProjection T.character (e.symm g)))
      map_one' := by
        apply Multiplicative.ext
        change q (heightProjection T.character (e.symm 1)) = 0
        rw [hzero, map_zero]
      map_mul' := by
        intro g h
        apply Multiplicative.ext
        change q (heightProjection T.character (e.symm (g * h))) =
          q (heightProjection T.character (e.symm g)) + q (heightProjection T.character (e.symm h))
        rw [hmul, map_add] }
  have hπExp (x) : (π (Exp x)).toAdd = q (heightProjection T.character x) := by
    change q (heightProjection T.character (e.symm (Exp x))) = _
    rw [← he, e.symm_apply_apply]
  refine ⟨π, ?_, hπExp, integrated_height_surjective T q Exp π hπExp,
    integrated_height_isQuotientMap T q Exp π hπExp e (fun x => (he x).symm)⟩
  exact ((q.toLinearMap.comp (heightProjection T.character)).continuous_of_finiteDimensional).comp
    e.symm.continuous

end Topological

section Metric

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [SecondCountableTopology G] [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [SecondCountableTopology G] in
theorem exists_lipschitz_canonical_height_of_representation
    (chains : LinearMetricChains G)
    (dixmier : DixmierExponentialInput (E := E) (G := G))
    (realize : ExponentialLinearRealizationInput (EG := E) (G := G))
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp) :
    ∃ π : G →* Multiplicative W,
      (∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) ∧
      Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y := by
  obtain ⟨e, he⟩ := (dixmier ⟨a, ⟨T⟩⟩).2 Exp hExp
  obtain ⟨m, _, ρ, j, hind, hρExp⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  have hρ : Function.Injective ρ := by
    intro x y hxy
    exact hind.injective (congrArg
      (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ => (u : Matrix (Fin m) (Fin m) ℝ)) hxy)
  obtain ⟨π, hπ, hπExp, hsurj, hquot⟩ :=
    exists_canonical_height_of_representation T q Exp hExp e he j ρ hρ hρExp
  exact ⟨π, hπExp, hsurj, hquot, continuous_height_lipschitz chains π hπ⟩

end Metric
end PolycyclicRecognition

end

end OAI
