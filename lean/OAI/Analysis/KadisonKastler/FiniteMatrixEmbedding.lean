import OAI.Analysis.KadisonKastler.FiniteGroupEmbedding
import OAI.Analysis.BoundedHochschild.SignedMatrixUnitaries
import OAI.Analysis.FactorGeneration.MatrixAlgebras

namespace OAI

/-! # Embedding a nearby full matrix algebra

A finite signed permutation group spans the matrix entries. Correcting that
group therefore moves the whole matrix algebra into the neighbour. The
displacement bound is independent of the matrix size.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H} {n : ℕ}

/-- The same concrete matrix units in the signed-group construction. -/
def matrixSystemOfUnits (E : Generator.MatrixUnitSystem (Fin n) (Algebra M)) :
    HochschildMatrixSystems.MatrixSystem (Algebra M) n where
  entry := E.entry
  star_entry := E.star_entry
  entry_mul := E.mul_entry
  sum_diagonal := E.total

/-- A full matrix stage in a one-sided near inclusion is unitarily embedded
in the neighbouring algebra, with a dimension-independent bound. -/
theorem exists_unitary_matrixStage_embedding
    (E : Generator.MatrixUnitSystem (Fin n) (Algebra M)) {γ : ℝ}
    (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152) (hnear : NearInclusion M N γ) :
    ∃ w : unitary (H →L[ℂ] H),
      (∀ x ∈ E.concreteAlgebra, unitaryConj w x ∈ N) ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
  let F := matrixSystemOfUnits E
  let G := F.signedPermutationGroup
  let : Fintype G := Fintype.ofFinite G
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let U : G →* unitary (Algebra M) := F.signedPermutationGroup.subtype
  obtain ⟨w, hw, hn⟩ := exists_unitary_finiteGroup_embedding_of_nearInclusion
    U hγ hsmall hnear
  let φ : Algebra M →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) w).toStarAlgHom.comp M.toStarSubalgebra.subtype
  let S : Submodule ℂ (Algebra M) :=
    N.toStarSubalgebra.toSubalgebra.toSubmodule.comap φ.toAlgHom.toLinearMap
  have hspan : Submodule.span ℂ
      (Set.range (fun g : G => (U g : Algebra M))) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact hw g
  have hentry (i j : Fin n) : φ (E.entry i j) ∈ N :=
    hspan (F.entry_mem_signedPermutation_span i j)
  refine ⟨w, ?_, hn⟩
  rintro x ⟨a, rfl⟩
  change φ (E.hom a) ∈ N
  rw [E.hom_apply, map_sum]
  apply N.toStarSubalgebra.sum_mem
  intro i _
  rw [map_sum]
  apply N.toStarSubalgebra.sum_mem
  intro j _
  change φ.toAlgHom.toLinearMap (a i j • E.entry i j) ∈ N
  rw [map_smul]
  exact N.toStarSubalgebra.smul_mem (hentry i j) _

/-- The preceding construction for an entire represented full matrix algebra. -/
theorem exists_unitary_finiteMatrix_embedding
    (E : Generator.MatrixUnitSystem (Fin n) (Algebra M))
    (hE : Function.Surjective E.hom) {γ : ℝ}
    (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152) (hnear : NearInclusion M N γ) :
    ∃ w : unitary (H →L[ℂ] H),
      (∀ x ∈ M, unitaryConj w x ∈ N) ∧ ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
  obtain ⟨w, hw, hn⟩ := exists_unitary_matrixStage_embedding E hγ hsmall hnear
  refine ⟨w, ?_, hn⟩
  intro x hx
  obtain ⟨a, ha⟩ := hE ⟨x, hx⟩
  exact hw x ⟨a, congrArg Subtype.val ha⟩

end

end KadisonKastler

end OAI
