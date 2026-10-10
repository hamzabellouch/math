import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilshadowGraphCover
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGroupNilpotence
import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeFiniteIndexEmbedding
import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeEmbedding
import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeTransport

namespace OAI

/-! # Connected realization of lattices in the original nonsplit extension -/

noncomputable section
namespace PolycyclicRecognition.IntegralNilshadowData
open scoped Manifold ContDiff
attribute [local instance] factorExtensionTopology semidirectProductTopology
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)

theorem uniform_lattice_realization
    (Γ : Subgroup (FactorExtension D.system)) (hΓ : IsUniformLattice Γ) :
    ∃ J : Subgroup Γ, J.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (J ≃* Λ) := by
  let : IsTopologicalGroup L := topologicalGroup_of_lieGroup (𝓘(ℝ, L)) ⊤
  let : IsTopologicalGroup (FactorExtension D.system) :=
    factorExtensionTopologicalGroup D.system (fun q => by
      have h := ((D.smooth q).comp (D.twist_smooth q)).continuous
      have heq : (fun x => D.removed q (D.twistedSystem.action q x)) = D.system.action q := by
        funext x
        exact (D.removed q).apply_symm_apply _
      change Continuous (fun x => D.removed q (D.twistedSystem.action q x)) at h
      rwa [heq] at h)
  let : Group.IsNilpotent D.completion.carrier := polynomial_group_nilpotent
  let : IsTopologicalGroup D.completion.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.completion.carrier)) ⊤
  obtain ⟨m, hm, φ, hφ, he, hinv, hfix⟩ := D.exists_real_action
  let := semidirectProductTopologicalGroup φ hφ.continuous
  let F := factorPullbackMap D.system (latticePowerHom n m)
  have hFi := factorPullbackMap_injective D.system (latticePowerHom n m)
    (latticePowerHom_injective n hm)
  have hFe := factorPowerMap_isClosedEmbedding D.system hm
  let := factorPowerMap_finiteIndex D.system hm
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
      exact congrArg (fun x : J => ((x : Γ) : FactorExtension D.system)) hab
    · intro j
      obtain ⟨x, hx⟩ := j.property
      have hxΓ : x ∈ Γm := by change F x ∈ Γ; rw [hx]; exact j.val.property
      refine ⟨⟨x, hxΓ⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hx
  let eJ : Γm ≃* J := MulEquiv.ofBijective fJ hfJ
  let ψ := D.powerGraphEmbedding hm φ he hinv
  have hψ := D.powerGraphEmbedding_isEmbedding hm φ he hinv
  obtain ⟨K, hK, hc⟩ := D.powerGraph_compact_cover hm φ he hinv hfix
  have hΛ := hΓm.map_of_compact_cover ψ hψ K hK hc
  let τ := D.inverseScaledHeight m
  let hτ := D.inverseScaledHeight_smooth m
  let hi := fun v x => congrArg (scaleRealHeight n (-((m : ℝ)⁻¹))) (hinv v x)
  let S := invariantGraphLieModel φ τ hi hφ hτ
  let eS := invariantGraphModelEquiv φ τ hi hφ hτ
  let Λ := (Γm.map ψ).comap eS.toMonoidHom
  have hΛS : IsUniformLattice Λ := hΛ.comap_mulEquiv eS
    (invariantGraphModelEquiv_continuous φ τ hi hφ hτ)
    (invariantGraphModelEquiv_symm_continuous φ τ hi hφ hτ)
  let eψ : Γm ≃* Γm.map ψ := Γm.equivMapOfInjective ψ hψ.injective
  exact ⟨J, hJ, S, Λ, hΛS,
    ⟨eJ.symm.trans (eψ.trans (comapSubgroupEquiv eS (Γm.map ψ)).symm)⟩⟩

end PolycyclicRecognition.IntegralNilshadowData

end

end OAI
