import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularGroupIntegration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RepresentedExponentialLogSmooth
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothFaithfulRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraRepresentationDerivative
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RiemannianExponentialInputs

namespace OAI

/-! # Smooth regularity from the topological Dixmier chart

Given a global exponential homeomorphism, the faithful triangular
representation and the injective differential of its exponential prove
smoothness of the chart and its inverse, as needed for metric comparison.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem dixmier_exponential_smooth_chart
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (dixmier : DixmierExponentialInput (E := E) (G := G))
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp) :
    let V := Fin (finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) → ℝ
    let b := finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
    ∃ φ : V ≃ₜ G,
      (∀ v, φ v = Exp (b.equivFun.symm v)) ∧
      ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ φ ∧
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ φ.symm := by
  let : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace E G
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨m, _hm, j, ρ, hj, _hu, _hn, hρ, _hρi, he⟩ :=
    exists_faithful_triangular_group_representation T dixmier Exp hExp
  let : TopologicalSpace (Matrix (Fin m) (Fin m) ℝ) :=
    (inferInstance : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ)).toMetricSpace
      |>.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : ChartedSpace (Matrix (Fin m) (Fin m) ℝ) (Matrix (Fin m) (Fin m) ℝ) :=
    chartedSpaceSelf _
  obtain ⟨chart, hchart⟩ := (dixmier ⟨a, ⟨T⟩⟩).2 Exp hExp
  let V := Fin (finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) → ℝ
  let b := finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
  let e : V ≃L[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G := b.equivFun.symm.toContinuousLinearEquiv
  let φ : V ≃ₜ G := e.toHomeomorph.trans chart
  have hφ (v : V) : φ v = Exp (b.equivFun.symm v) := hchart _
  have hsρ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, Matrix (Fin m) (Fin m) ℝ)) ∞
      (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) :=
    contMDiff_of_continuous_unitsHom hExp ρ (Units.continuous_val.comp hρ)
  have hjρ : unitsHomLieDifferential ρ hsρ = j := by
    apply LieHom.ext
    intro x
    apply unitsHomLieDifferential_eq_of_exponential_line hExp ρ hsρ x (j x)
    intro t
    simpa only [map_smul] using he (t • x)
  let D : E →L[ℝ] Matrix (Fin m) (Fin m) ℝ := j.toLinearMap.toContinuousLinearMap
  have hD : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, Matrix (Fin m) (Fin m) ℝ))
      (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) 1 D := by
    have hh := hasMFDerivAt_unitsHomLieDifferential ρ hsρ
    rw [hjρ] at hh
    exact hh
  have hDi : Function.Injective D := hj
  let J : V →L[ℝ] Matrix (Fin m) (Fin m) ℝ :=
    (j.toLinearMap.comp b.equivFun.symm.toLinearMap).toContinuousLinearMap
  have hcoords (v : V) : (ρ (φ v) : Matrix (Fin m) (Fin m) ℝ) = NormedSpace.exp (J v) := by
    rw [hφ, he]
    rfl
  have hc : ContDiff ℝ ∞ (fun v : V => NormedSpace.exp (J v)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro v
    exact (NormedSpace.exp_analytic (𝕂 := ℝ) (J v)).contDiffAt.comp v J.contDiff.contDiffAt
  have hρφ : ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, Matrix (Fin m) (Fin m) ℝ)) ∞
      (fun v => (ρ (φ v) : Matrix (Fin m) (Fin m) ℝ)) := by
    have hh := hc.contMDiff
    have hfun : (fun v => (ρ (φ v) : Matrix (Fin m) (Fin m) ℝ)) =
        (fun v => NormedSpace.exp (J v)) := funext hcoords
    rwa [← hfun] at hh
  refine ⟨φ, hφ, ?_, ?_⟩
  · intro v
    exact contMDiffAt_of_unitsHom_injective_differential ρ hsρ D hD hDi
      φ.continuous.continuousAt (hρφ v)
  · apply contMDiff_inverse_exponential_chart_of_triangular T j hj b.equivFun.symm φ
      (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) hsρ
    intro v
    exact hcoords v

/-- The smooth regularity needed by the metric application is derived; only
a global topological exponential chart is a hypothesis. -/
theorem dixmierExponentialDiffeomorphismInput_of_topological
    (dixmier : DixmierExponentialInput (E := E) (G := G)) :
    DixmierExponentialDiffeomorphismInput (E := E) (G := G) := by
  intro a T Exp hExp
  exact dixmier_exponential_smooth_chart T dixmier Exp hExp

end PolycyclicRecognition

end

end OAI
