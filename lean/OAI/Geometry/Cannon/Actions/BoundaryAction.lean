import Mathlib
import OAI.Geometry.Cannon.Conformal.BoundaryUniformQuasiMobius
import OAI.Geometry.Cannon.Conformal.GeometricConformalAction

namespace OAI

section
section
section
noncomputable section
namespace CannonRelease

universe u

def MainObligation : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (D : CayleyData G), D.ThinTriangles → Nonempty (Boundary D ≃ₜ SphereTwo) →
    ∃ ρ : G →* H3Isom, ProperAction ρ ∧ CocompactAction ρ ∧
      (ρ.ker : Set G).Finite

end CannonRelease

namespace CannonRelease
open Set

universe v
variable {G : Type v} [Group G]

theorem CayleyData.countable (D : CayleyData G) : Countable G := by
  apply Set.countable_univ_iff.mp
  have hfin (n : ℕ) : {g : G | D.graph.dist 1 g ≤ n}.Finite :=
    CannonGraph.finite_graph_ball D.connected (CannonGraph.finite_cayley_neighbors D.generators) 1 n
  have hcover : (⋃ n : ℕ, {g : G | D.graph.dist 1 g ≤ n}) = univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro g
    exact Set.mem_iUnion.mpr ⟨D.graph.dist 1 g,by change D.graph.dist 1 g ≤ D.graph.dist 1 g; rfl⟩
  rw [← hcover]
  exact Set.countable_iUnion (fun n => (hfin n).countable)

end CannonRelease

end
end
noncomputable section
namespace CannonRelease
open CannonGraph CannonVisual CannonQM CannonActions CannonMobius CannonH3

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniformized_action (ψ : Boundary D ≃ₜ Sphere) :
    let _ := visualMetricSpace D hδ
    QuasiMobius ψ →
    ∃ ρ : G →* H3Isom, ProperAction ρ ∧ CocompactAction ρ ∧ (ρ.ker : Set G).Finite := by
  let _ := visualMetricSpace D hδ
  dsimp only
  intro hψ
  let : Countable G := D.countable
  obtain ⟨η,hη⟩ := boundary_uniform_conjugates D hδ ψ hψ
  let A := boundaryAction D ⟨δ,hδ⟩
  obtain ⟨F,hF⟩ := sphere_action_straightening (conjugate ψ A) hη
  apply boundary_conformal_action D hδ (ψ.trans F)
  intro g
  have he : conjugate (ψ.trans F) (boundaryAction D ⟨δ,hδ⟩) g =
      F*conjugate ψ A g*F.symm := by
    ext z
    rfl
  simpa only [he] using hF g

end CannonRelease

namespace CannonRelease
open CannonGraph CannonVisual CannonQM CannonMobius

universe w
variable {G : Type w} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_round_uniformized_action (ψ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    QuasiMobius ψ →
    ∃ ρ : G →* H3Isom, ProperAction ρ ∧ CocompactAction ρ ∧ (ρ.ker : Set G).Finite := by
  let _ := visualMetricSpace D hδ
  dsimp only
  intro hψ
  have hround : QuasiMobius roundChart.symm := by
    refine ⟨OrderIso.refl _,?_⟩
    intro x y z w hh
    change crossRatio (roundChart.symm x) (roundChart.symm y)
      (roundChart.symm z) (roundChart.symm w) ≤ crossRatio x y z w
    have he := roundChart_crossRatio (roundChart.symm x) (roundChart.symm y)
      (roundChart.symm z) (roundChart.symm w)
    simpa only [roundChart.apply_symm_apply] using he.ge
  exact boundary_uniformized_action D hδ (ψ.trans roundChart.symm)
    (hround.comp hψ ψ.injective)

end CannonRelease

end
end
end

end OAI
