import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommonEigenvectors
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InvariantSubspaceDeterminant

namespace OAI

/-! # A commutator acts trivially on a common eigenspace -/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement
variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

theorem commonEigenspace_invariant (ρ : G →* (V ≃ₗ[K] V)) (χ : G → K) :
    ∀ g : G, ∀ v ∈ commonEigenspace (fun g => (ρ g).toLinearMap) χ,
      ρ g v ∈ commonEigenspace (fun g => (ρ g).toLinearMap) χ := by
  intro g v hv
  change (ρ g).toLinearMap v ∈ _
  rw [(mem_commonEigenspace _ _ _).mp hv g]
  exact Submodule.smul_mem _ _ hv

theorem commutator_fixes_commonEigenspace (ρ : G →* (V ≃ₗ[K] V)) (χ : G → K)
    (a : commutator G) (v : V)
    (hv : v ∈ commonEigenspace (fun g => (ρ g).toLinearMap) χ) : ρ a v = v := by
  let W := commonEigenspace (fun g => (ρ g).toLinearMap) χ
  let R := invariantSubspaceAction ρ W (commonEigenspace_invariant ρ χ)
  have hscalar (g : G) : (R g).toLinearMap = χ g • (1 : Module.End K W) :=
    invariantSubspaceAction_scalar ρ W _ g (χ g) (fun v hv =>
      (mem_commonEigenspace _ _ _).mp hv g)
  have hcomm (g h : G) : Commute (R g) (R h) := by
    change R g * R h = R h * R g
    apply LinearEquiv.toLinearMap_injective
    change (R g).toLinearMap * (R h).toLinearMap =
      (R h).toLinearMap * (R g).toLinearMap
    rw [hscalar, hscalar]
    simp [smul_smul, mul_comm]
  have hle : commutator G ≤ R.ker := by
    rw [_root_.commutator_def]
    apply Subgroup.commutator_le.mpr
    intro g _ h _
    change R ⁅g, h⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (hcomm g h)
  have ha : R a = 1 := hle a.property
  exact congrArg (fun f : W ≃ₗ[K] W => (f ⟨v, hv⟩ : V)) ha

end PolycyclicRecognition

end

end OAI
