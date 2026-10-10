import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothIntegralActionExtension
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntegralSemidirectEmbedding
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntegralSemidirectPowerTopology
import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeFiniteIndexEmbedding
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionTopology

namespace OAI

/-! # Realizing a uniform lattice with possibly translated integral fibers

A smooth action of an integral vector group extends after a finite power.
Any uniform lattice in the original semidirect group then has a finite-index
subgroup which is a uniform lattice in the connected solvable Lie model.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
attribute [local instance] semidirectProductTopology
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [PolynomialExponentialCoordinates L] [Group.IsSolvable L]

theorem smooth_integral_uniform_lattice_realization {n : ℕ}
    (ρ : IntegralLatticeGroup n →* MulAut L)
    (hρ : ∀ z, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (ρ z))
    (Γ : Subgroup (L ⋊[ρ] IntegralLatticeGroup n)) (hΓ : IsUniformLattice Γ) :
    ∃ J : Subgroup Γ, J.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (J ≃* Λ) := by
  let : IsTopologicalGroup L := topologicalGroup_of_lieGroup (𝓘(ℝ, L)) ⊤
  have hρc : Continuous (fun p : IntegralLatticeGroup n × L => ρ p.1 p.2) :=
    continuous_discrete_parameter (fun z x => ρ z x) (fun z => (hρ z).continuous)
  let := semidirectProductTopologicalGroup ρ hρc
  obtain ⟨m, hm, φ, hφ, he⟩ := smooth_integral_action_has_vector_extension ρ hρ
  let F := integralSemidirectPowerMap ρ m
  have hFi := integralSemidirectPowerMap_injective ρ hm
  have hFe := integralSemidirectPowerMap_isClosedEmbedding ρ hm
  let := integralSemidirectPowerMap_finiteIndex ρ hm
  let Γm := Γ.comap F
  have hΓm : IsUniformLattice Γm := hΓ.comap_finiteIndex F hFe
  let J := F.range.comap Γ.subtype
  have hJ : J.FiniteIndex := inferInstance
  let f0 : Γm →* Γ := (F.comp Γm.subtype).codRestrict Γ (fun x => x.property)
  let fJ : Γm →* J := f0.codRestrict J (fun x => ⟨x.val, rfl⟩)
  have hfJ : Function.Bijective fJ := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply hFi
      exact congrArg (fun x : J => ((x : Γ) : L ⋊[ρ] IntegralLatticeGroup n)) hab
    · intro j
      obtain ⟨x, hx⟩ := j.property
      have hxΓ : x ∈ Γm := by change F x ∈ Γ; rw [hx]; exact j.val.property
      refine ⟨⟨x, hxΓ⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hx
  let eJ : Γm ≃* J := MulEquiv.ofBijective fJ hfJ
  let E := integralSemidirectEmbedding (ρ.comp (latticePowerHom n m)) φ he
  have hEc : Continuous (fun p : Multiplicative (Fin n → ℝ) × L => φ p.1 p.2) :=
    hφ.continuous
  have hΛ := uniformLattice_integralSemidirect_image (ρ.comp (latticePowerHom n m)) φ he hEc hΓm
  let T := smoothVectorActionModel φ hφ
  let eT := smoothVectorActionModelEquiv φ hφ
  let Λ := (Γm.map E).comap eT.toMonoidHom
  have hΛT : IsUniformLattice Λ := hΛ.comap_mulEquiv eT
    (smoothVectorActionModelEquiv_continuous φ hφ)
    (smoothVectorActionModelEquiv_symm_continuous φ hφ)
  let eE : Γm ≃* Γm.map E := Γm.equivMapOfInjective E
    (integralSemidirectEmbedding_isEmbedding _ _ _).injective
  exact ⟨J, hJ, T, Λ, hΛT,
    ⟨eJ.symm.trans (eE.trans (comapSubgroupEquiv eT (Γm.map E)).symm)⟩⟩

end PolycyclicRecognition

end

end OAI
