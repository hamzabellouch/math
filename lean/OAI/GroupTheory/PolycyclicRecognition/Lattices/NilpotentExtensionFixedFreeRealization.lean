import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentExtensionLangSplitting
import OAI.GroupTheory.PolycyclicRecognition.Lattices.SmoothIntegralLatticeRealization
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SplitFactorTopology

namespace OAI

/-! # Connected realization of nonsplit extensions with a fixed-point-free lift

The quotient lift is allowed to have nontrivial commutators. The Lang inverse
constructs a splitting only after the nilpotent kernel has been completed.
-/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
open scoped Manifold ContDiff
attribute [local instance] factorExtensionTopology semidirectProductTopology
variable {N G : Type} [Group N] [Group G] (C : NilpotentLatticeCoordinates N)
  {n : ℕ} (S : GroupExtension N G (IntegralLatticeGroup n))
  (σ : S.Section) (hσ : σ 1 = 1)

include hσ

/-- A concrete sufficient condition for the general nonsplit realization:
one quotient lift acts without fixed vectors on the completed kernel. -/
theorem extension_realization_of_fixedPointFree_lift (q : IntegralLatticeGroup n)
    (hA : Function.Bijective
      (fun x : C.carrier => C.automorphismLinear (S.conjAct (σ q)) x - x)) :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ∃ (R : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup R.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ) := by
  let T := C.extensionFactorSystem S σ hσ
  let s := C.completedExtensionSplitting S σ hσ q hA
  let ρ := s.conjAct
  let e := splitFactorEquiv T s
  let Γ := C.completedExtensionLattice S σ hσ
  let Γs := Γ.comap e.toMonoidHom
  let : IsTopologicalGroup C.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, C.carrier)) ⊤
  have hΓs : IsUniformLattice Γs := (C.completedExtensionLattice_uniform S σ hσ).comap_mulEquiv e
    (splitFactorEquiv_continuous T s (fun z => (C.extensionFactorSystem_smooth S σ hσ z).continuous))
    (splitFactorEquiv_symm_continuous T s)
  have hρ : ∀ z, ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ (ρ z) :=
    C.completedExtensionSplitting_action_smooth S σ hσ s
  obtain ⟨J, hJ, R, Λ, hΛ, ⟨f⟩⟩ := smooth_integral_uniform_lattice_realization ρ hρ Γs hΓs
  let eG : G ≃* Γs := (C.completedExtensionLatticeEquiv S σ hσ).trans
    (comapSubgroupEquiv e Γ).symm
  let K := J.comap eG.toMonoidHom
  let := hJ
  have hK : K.FiniteIndex := inferInstance
  exact ⟨K, hK, R, Λ, hΛ, ⟨(comapSubgroupEquiv eG J).trans f⟩⟩

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
