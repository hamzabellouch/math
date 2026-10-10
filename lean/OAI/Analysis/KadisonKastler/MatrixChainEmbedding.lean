import OAI.Analysis.KadisonKastler.CompatibleMatrixFrames
import OAI.Analysis.KadisonKastler.IncreasingGroupEmbedding

namespace OAI

/-! # Embedding an increasing full-matrix closure

Compatible frames give an increasing sequence of finite unitary groups.
Their union generates the original von Neumann algebra, so its invariant
mean provides a single simultaneous embedding of the entire closure.
-/

namespace KadisonKastler

noncomputable section

variable {U : Type*} [Group U]

/-- The union of a monotone sequence of subgroups, as a subgroup. -/
def increasingSubgroupUnion (K : ℕ → Subgroup U) (hK : Monotone K) : Subgroup U where
  carrier := {u | ∃ n, u ∈ K n}
  one_mem' := ⟨0, (K 0).one_mem⟩
  mul_mem' := by
    rintro a b ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨max n m, (K (max n m)).mul_mem
      (hK (Nat.le_max_left n m) hn) (hK (Nat.le_max_right n m) hm)⟩
  inv_mem' := by
    rintro a ⟨n, hn⟩
    exact ⟨n, (K n).inv_mem hn⟩

/-- The original stages, regarded inside their union. -/
def increasingUnionStage (K : ℕ → Subgroup U) (hK : Monotone K) (n : ℕ) :
    Subgroup (increasingSubgroupUnion K hK) :=
  (K n).comap (increasingSubgroupUnion K hK).subtype

instance increasingUnionStage_finite (K : ℕ → Subgroup U) (hK : Monotone K)
    [∀ n, Finite (K n)] (n : ℕ) : Finite (increasingUnionStage K hK n) := by
  let f : increasingUnionStage K hK n → K n := fun u => ⟨u.val.val, u.property⟩
  exact Finite.of_injective f (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun u : K n => (u : U)) h)))

theorem increasingUnionStage_monotone (K : ℕ → Subgroup U) (hK : Monotone K) :
    Monotone (increasingUnionStage K hK) := by
  intro n m hnm u hu
  exact hK hnm hu

theorem increasingUnionStage_covers (K : ℕ → Subgroup U) (hK : Monotone K)
    (u : increasingSubgroupUnion K hK) : ∃ n, u ∈ increasingUnionStage K hK n :=
  u.property

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Regard an ambient unitary subgroup contained in an algebra as internal unitaries. -/
def subgroupAlgebraRepresentation (G : Subgroup (unitary (H →L[ℂ] H)))
    (M : VonNeumannAlgebra H) (hG : ∀ u : G, (u : H →L[ℂ] H) ∈ M) :
    G →* unitary (Algebra M) where
  toFun u := algebraUnitaryOfMem u.val (hG u)
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)

variable [Nontrivial H] {A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)}

/-- Every element of the finite-group union belongs to the original matrix closure. -/
theorem matrixChainGroup_mem (F : ∀ n, FullMatrixFrame (A n)) (hA : Monotone A)
    (u : increasingSubgroupUnion
      (fun n => (compatibleMatrixFrames F hA n).group)
      (compatibleMatrixFrames_group_monotone F hA)) :
    (u : H →L[ℂ] H) ∈ generatedVonNeumannAlgebra (⨆ n, A n) := by
  obtain ⟨n, hn⟩ := u.property
  apply subset_generatedVonNeumannAlgebra
  exact (le_iSup A n) ((compatibleMatrixFrames F hA n).group_mem ⟨u.val, hn⟩)

/-- The increasing union of finite frame groups generates the entire matrix closure. -/
theorem matrixChainGroup_generates (F : ∀ n, FullMatrixFrame (A n)) (hA : Monotone A) :
    generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (Set.range (fun u =>
      (subgroupAlgebraRepresentation _ _ (matrixChainGroup_mem F hA) u : H →L[ℂ] H)))) =
      generatedVonNeumannAlgebra (⨆ n, A n) := by
  let G := increasingSubgroupUnion (fun n => (compatibleMatrixFrames F hA n).group)
    (compatibleMatrixFrames_group_monotone F hA)
  let R := generatedVonNeumannAlgebra (⨆ n, A n)
  let V := subgroupAlgebraRepresentation G R (matrixChainGroup_mem F hA)
  let Q := generatedVonNeumannAlgebra
    (StarAlgebra.adjoin ℂ (Set.range (fun u : G => (V u : H →L[ℂ] H))))
  change Q = R
  apply le_antisymm
  · apply generatedVonNeumannAlgebra_le_of_le
    apply StarAlgebra.adjoin_le
    rintro _ ⟨u, rfl⟩
    exact (V u).val.property
  · apply generatedVonNeumannAlgebra_le_of_le
    apply iSup_le
    intro n a ha
    change a ∈ (Q : Set (H →L[ℂ] H))
    rw [← Q.centralizer_centralizer]
    intro T hT
    have hc := (compatibleMatrixFrames F hA n).commutes_of_group T (by
      intro u
      let g : G := ⟨u.val, ⟨n, u.property⟩⟩
      have hg : (u : H →L[ℂ] H) ∈ Q :=
        subset_generatedVonNeumannAlgebra _ (StarAlgebra.subset_adjoin ℂ _ ⟨g, rfl⟩)
      exact hT _ hg)
    exact (hc a ha).symm

/-- The whole increasing matrix closure embeds with a dimension-independent
near-identity bound. No injectivity or amenable embedding hypothesis is used. -/
theorem exists_unitary_matrixChain_embedding
    (F : ∀ n, FullMatrixFrame (A n)) (hA : Monotone A)
    {N : VonNeumannAlgebra H} {γ : ℝ} (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152)
    (hnear : NearInclusion (generatedVonNeumannAlgebra (⨆ n, A n)) N γ) :
    ∃ w : unitary (H →L[ℂ] H),
      (∀ x ∈ generatedVonNeumannAlgebra (⨆ n, A n), unitaryConj w x ∈ N) ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
  let K := fun n => (compatibleMatrixFrames F hA n).group
  let hK := compatibleMatrixFrames_group_monotone F hA
  let G := increasingSubgroupUnion K hK
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  exact exists_unitary_embedding_of_increasing_finite_groups
    (increasingUnionStage K hK) (increasingUnionStage_monotone K hK)
    (increasingUnionStage_covers K hK)
    (subgroupAlgebraRepresentation G _ (matrixChainGroup_mem F hA))
    (matrixChainGroup_generates F hA) hγ hsmall hnear

end

end KadisonKastler

end OAI
