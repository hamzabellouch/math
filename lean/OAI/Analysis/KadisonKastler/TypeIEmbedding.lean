import OAI.Analysis.KadisonKastler.TypeICyclicGeneration
import OAI.Analysis.KadisonKastler.HilbertMatrixGeneration
import OAI.Analysis.KadisonKastler.FiniteMatrixEmbedding

namespace OAI

/-! # Constructed near inclusions for represented type I factors

Finite signed permutation groups, or their increasing union in the countable
case, generate the minimal cyclic representation. Weak generation transports
back to the original representation before applying the group correction.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- The type I embedding needed by stability, constructed without the general
amenable embedding input. -/
theorem exists_unitary_typeI_embedding {M N : VonNeumannAlgebra H}
    (hM : IsTypeIFactor M) {γ : ℝ} (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152)
    (hnear : NearInclusion M N γ) :
    ∃ w : unitary (H →L[ℂ] H), (∀ x ∈ M, unitaryConj w x ∈ N) ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
  classical
  obtain ⟨p, hp⟩ := hM.minimal
  obtain ⟨ξ, hξ, hpξ⟩ := exists_nonzero_fixed_vector p hp.1
  let K := typeICyclicSpace M ξ
  let e := typeICyclicEquiv hM.factor p hp ξ hξ hpξ
  rcases separable_hilbertBasis_dichotomy (H := K) with hfinite | hinfinite
  · obtain ⟨n, ⟨b⟩⟩ := hfinite
    let E := (orthonormalMatrixUnits b).map e.symm.toStarAlgHom
    have hE : Function.Surjective E.hom := by
      intro a
      obtain ⟨c, hc⟩ := orthonormalMatrixUnits_surjective b (e a)
      refine ⟨c, ?_⟩
      rw [matrixUnits_map_hom, hc]
      exact e.symm_apply_apply a
    exact exists_unitary_finiteMatrix_embedding E hE hγ hsmall hnear
  · obtain ⟨b⟩ := hinfinite
    let F := hilbertBasisFullCorner b
    let D := F.finiteSignedGroup
    let hD := F.finiteSignedGroup_monotone
    let G : Type _ := increasingSubgroupUnion D hD
    let : TopologicalSpace G := ⊥
    let : DiscreteTopology G := ⟨rfl⟩
    let U : G →* unitary (K →L[ℂ] K) := (increasingSubgroupUnion D hD).subtype
    have hgen : ∀ T : K →L[ℂ] K, T ∈ generatedVonNeumannAlgebra
        (StarAlgebra.adjoin ℂ (Set.range (fun g => (U g : K →L[ℂ] K)))) := by
      intro T
      change T ∈ generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ
        (Set.range (fun g => (subgroupAlgebraRepresentation F.signedGroupUnion
          F.scalarMatrixAlgebra F.signedGroupUnion_mem g : K →L[ℂ] K))))
      rw [F.signedGroupUnion_generates]
      exact hilbertBasisFullCorner_mem_scalar b T
    exact exists_unitary_embedding_of_invariant_group
      (increasingFiniteScalarInvariantMean (increasingUnionStage D hD)
        (increasingUnionStage_monotone D hD) (increasingUnionStage_covers D hD))
      (typeICyclicGroup hM.factor p hp ξ hξ hpξ U)
      (typeICyclicGroup_generates hM.factor p hp ξ hξ hpξ U hgen) hγ hsmall hnear

end

end KadisonKastler

end OAI
