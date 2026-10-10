import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilshadowLatticeRealization
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SectionFactorTopology
import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentExtensionLattice

namespace OAI

/-! # Connected realization without a splitting or a fixed-point-free action -/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
open scoped Manifold ContDiff
attribute [local instance] factorExtensionTopology
variable {N G : Type} [Group N] [Group G] (C : NilpotentLatticeCoordinates N)
  {n : ℕ} (E : GroupExtension N G (IntegralLatticeGroup n))
  (σ : E.Section) (hσ : σ 1 = 1)

include C E σ hσ in
theorem extension_realization :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ) := by
  let T := C.extensionFactorSystem E σ hσ
  let E' := FactorExtension.groupExtension T
  obtain ⟨D⟩ := exists_integralNilshadowData E'
    (factorSystem_conjugation_smooth T (C.extensionFactorSystem_smooth E σ hσ))
  let : IsTopologicalGroup C.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, C.carrier)) ⊤
  let e := GroupExtensionSection.mulEquiv E' D.sectionMap D.normalized
  let Γ := C.completedExtensionLattice E σ hσ
  let Γ' := Γ.comap e.symm.toMonoidHom
  have hΓ' : IsUniformLattice Γ' := (C.completedExtensionLattice_uniform E σ hσ).comap_mulEquiv
    e.symm (sectionFactorEquiv_symm_continuous T D.sectionMap D.normalized)
      (sectionFactorEquiv_continuous T D.sectionMap D.normalized)
  obtain ⟨J, hJ, S, Λ, hΛ, ⟨f⟩⟩ := D.uniform_lattice_realization Γ' hΓ'
  let eG : G ≃* Γ' := (C.completedExtensionLatticeEquiv E σ hσ).trans
    (comapSubgroupEquiv e.symm Γ).symm
  let K := J.comap eG.toMonoidHom
  let := hJ
  have hK : K.FiniteIndex := inferInstance
  exact ⟨K, hK, S, Λ, hΛ, ⟨(comapSubgroupEquiv eG J).trans f⟩⟩

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
