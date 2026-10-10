import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularGroupIntegration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularLocalLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationTopology

namespace OAI

/-! # Constructing the full triangular realization from the exponential chart

The representation is obtained from the nilshadow and the two Cartan
factors. The topology is recovered from the unique local logarithm in the
real upper triangular algebra. Thus Onshuus–Post is no longer an independent
input once the separately named Dixmier exponential chart is available.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem onshuusPostRealizationInput_of_dixmier
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (dixmier : DixmierExponentialInput (E := E) (G := G)) :
    OnshuusPostRealizationInput T := by
  let : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace E G
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  intro Exp hExp
  obtain ⟨m, hm, j, ρ, hj, hu, hn, hρ, _, he⟩ :=
    exists_faithful_triangular_group_representation T dixmier Exp hExp
  obtain ⟨chart, hchart⟩ := (dixmier ⟨a, ⟨T⟩⟩).2 Exp hExp
  have hsurj : Function.Surjective Exp := by
    intro g
    obtain ⟨x, hx⟩ := chart.surjective g
    exact ⟨x, (hchart x).symm.trans hx⟩
  let S := Matrix.blockTriangularSubalgebra ℝ ℝ (id : Fin m → Fin m)
  let jE : E →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ := j.toLinearMap
  let jS : E →ₗ[ℝ] S := jE.codRestrict S.toSubmodule (fun x => hu x)
  have hjS : Function.Injective jS := by
    intro x y h
    exact hj (congrArg Subtype.val h)
  let chartE : E ≃ₜ G := chart
  have hzero : chartE 0 = 1 := (hchart 0).trans hExp.map_zero
  have heS (x : E) : (ρ (chartE x) : Matrix (Fin m) (Fin m) ℝ) =
      (NormedSpace.exp (jS x) : S) := by
    rw [realTriangularAlgebra_coe_exp]
    change (ρ (chart x) : Matrix (Fin m) (Fin m) ℝ) = NormedSpace.exp (j x)
    have h := congrArg Units.val (he x)
    simp only [coe_algebraExpUnit] at h
    exact (congrArg (fun g : G => (ρ g : Matrix (Fin m) (Fin m) ℝ)) (hchart x)).trans h
  have hind := inducing_of_exponential_chart_and_local_logarithm S chartE hzero jS hjS
    ρ hρ heS realTriangularAlgebra_exp_kernel
  have hmatrix : Topology.IsInducing (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) :=
    Units.isOpenEmbedding_val.isInducing.comp hind
  have hpos (g : G) : ρ g ∈ positiveTriangular m := by
    obtain ⟨x, rfl⟩ := hsurj g
    rw [he]
    exact (positiveTriangularExp (j x) (hu x)).property
  let σ : G →* positiveTriangular m := ρ.codRestrict (positiveTriangular m) hpos
  refine ⟨m, hm, σ, hmatrix, ?_⟩
  intro x hx
  change StrictUpper ((ρ (Exp x) : Matrix (Fin m) (Fin m) ℝ) - 1)
  rw [he, coe_algebraExpUnit]
  exact triangular_nilpotent_exp_unipotent (j x) (hu x) (hn x hx)

end PolycyclicRecognition

end

end OAI
