import Mathlib
import OAI.Geometry.Cannon.Actions.Triples
import OAI.Geometry.Cannon.Conformal.FiniteB
import OAI.Geometry.Cannon.Actions.Proper

namespace OAI

section
section
section
noncomputable section
noncomputable section
open Set Filter Topology
open scoped OnePoint

noncomputable section
open Set Filter Topology

namespace CannonH3
open CannonMobius CannonActions CannonRelease

variable {G : Type*} [Group G]

theorem geometric_conformal_action (σ : G →* (Sphere ≃ₜ Sphere))
    (hσ : ∀ g, σ g ∈ biholomorphic ∨ boundaryReflection*σ g ∈ biholomorphic)
    (hP : Proper (triplesAction σ)) (hC : Cocompact (triplesAction σ)) :
    ProperAction (conformalActionExtension σ hσ) ∧ CocompactAction (conformalActionExtension σ hσ) ∧
      ((conformalActionExtension σ hσ).ker : Set G).Finite := by
  let ρ := conformalActionExtension σ hσ
  let B : G →* (HyperbolicThree ≃ₜ HyperbolicThree) := hyperbolicIsometries.subtype.comp ρ
  let p : Triple → HyperbolicThree := coords.symm ∘ center
  have hp : IsProperMap p := coords.symm.isProperMap.comp proper_center
  have hs : Function.Surjective p := coords.symm.surjective.comp center_surjective
  have he (g : G) (t : Triple) : p (triplesAction σ g t)= B g (p t) := by
    change coords.symm (center (tripleMap (σ g) t))=(ρ g).val (coords.symm (center t))
    rw [center_conformal _ (hσ g)]
    change coords.symm (coords ((extensionHom ⟨σ g,conformal_or_anticonformal_mem (hσ g)⟩).val
      (coords.symm (center t))))=_
    rw [coords.symm_apply_apply]
    rfl
  have hBP : Proper B := proper_descends hp hs he hP
  have hBC : Cocompact B := cocompact_descends hp.continuous hs he hC
  refine ⟨hBP,hBC,?_⟩
  let _ : Nonempty HyperbolicThree := ⟨coords.symm basepoint⟩
  apply (proper_finite_kernel hBP).subset
  intro g hg
  change B g=1
  change ρ g=1 at hg
  change (ρ g).val=1
  rw [hg]
  rfl
end CannonH3

namespace CannonRelease
open CannonGraph CannonVisual CannonActions CannonMobius CannonH3

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_conformal_action (ψ : Boundary D ≃ₜ Sphere)
    (hψ : ∀ g, conjugate ψ (boundaryAction D ⟨δ,hδ⟩) g ∈ biholomorphic ∨
      boundaryReflection*conjugate ψ (boundaryAction D ⟨δ,hδ⟩) g ∈ biholomorphic) :
    ∃ ρ : G →* H3Isom, ProperAction ρ ∧ CocompactAction ρ ∧ (ρ.ker : Set G).Finite := by
  let _ := visualMetricSpace D hδ
  let A := boundaryAction D ⟨δ,hδ⟩
  let σ := conjugate ψ A
  have hP : Proper (triplesAction A) := boundary_triples_proper D hδ
  have hC : Cocompact (triplesAction A) := boundary_triples_cocompact D hδ
  have hPσ : Proper (triplesAction σ) := by
    rw [show σ=conjugate ψ A from rfl,triples_conjugate]
    exact proper_conjugate (triplesCongr ψ) hP
  have hCσ : Cocompact (triplesAction σ) := by
    rw [show σ=conjugate ψ A from rfl,triples_conjugate]
    exact cocompact_conjugate (triplesCongr ψ) hC
  exact ⟨conformalActionExtension σ hψ,geometric_conformal_action σ hψ hPσ hCσ⟩
end CannonRelease

end
end
end
end
end
end

end OAI
