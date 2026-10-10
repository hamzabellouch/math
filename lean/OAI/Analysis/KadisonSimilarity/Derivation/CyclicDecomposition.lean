import OAI.Analysis.KadisonSimilarity.Derivation.CyclicSummandColumns
import OAI.Analysis.KadisonSimilarity.Derivation.CyclicFactorization
import OAI.Analysis.KadisonSimilarity.Tracial.FullColumnTheorem
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Order.Zorn

namespace OAI

/-! Every unital star representation is the orthogonal sum of cyclic reducing
representations. The family is constructed by Zorn's lemma. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem self_mem_orbitClosure (N : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    ξ ∈ orbitClosure N ξ := by
  apply (LinearMap.range (orbitLinearMap N ξ)).le_topologicalClosure
  exact ⟨1, by simp⟩

/-- Orthogonality to one reducing cyclic subspace persists on the whole orbit
of a vector, including its closure. -/
theorem orbitClosure_le_orthogonal (N : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ η : H)
    (hξ : ξ ∈ (orbitClosure N η).toSubmodule.orthogonal) :
    (orbitClosure N ξ).toSubmodule ≤ (orbitClosure N η).toSubmodule.orthogonal := by
  apply (LinearMap.range (orbitLinearMap N ξ)).topologicalClosure_minimal ?_
    (Submodule.isClosed_orthogonal _)
  rintro x ⟨a, rfl⟩
  intro y hy
  change inner ℂ y ((a : H →L[ℂ] H) ξ) = 0
  rw [← ContinuousLinearMap.adjoint_inner_left]
  apply hξ
  exact orbitClosure_invariant N η (star a) y hy

/-- Pairwise orthogonality of the full closed cyclic spaces. -/
def CyclicOrbitOrthogonal (N : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ η : H) : Prop :=
  ∀ x ∈ orbitClosure N ξ, ∀ y ∈ orbitClosure N η, inner ℂ x y = 0

theorem cyclicOrbitOrthogonal_symm (N : StarSubalgebra ℂ (H →L[ℂ] H)) {ξ η : H}
    (h : CyclicOrbitOrthogonal N ξ η) : CyclicOrbitOrthogonal N η ξ := by
  intro x hx y hy
  exact inner_eq_zero_symm.mp (h y hy x hx)

def OrthogonalCyclicFamily (N : StarSubalgebra ℂ (H →L[ℂ] H)) (S : Set H) : Prop :=
  (∀ ξ ∈ S, ξ ≠ 0) ∧ S.Pairwise (CyclicOrbitOrthogonal N)

def cyclicFamilySpan (N : StarSubalgebra ℂ (H →L[ℂ] H)) (S : Set H) : Submodule ℂ H :=
  Submodule.span ℂ (⋃ ξ ∈ S, (orbitClosure N ξ : Set H))

theorem orbitClosure_le_cyclicFamilySpan (N : StarSubalgebra ℂ (H →L[ℂ] H))
    {S : Set H} {ξ : H} (hξ : ξ ∈ S) : (orbitClosure N ξ).toSubmodule ≤ cyclicFamilySpan N S := by
  intro x hx
  apply Submodule.subset_span
  exact Set.mem_iUnion.mpr ⟨ξ, Set.mem_iUnion.mpr ⟨hξ, hx⟩⟩

theorem exists_maximal_orthogonalCyclicFamily (N : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ∃ S : Set H, Maximal (OrthogonalCyclicFamily N) S := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c, ?_, ?_⟩
  · constructor
    · intro ξ hξ
      obtain ⟨S, hS, hξ⟩ := Set.mem_sUnion.mp hξ
      exact (hc hS).1 ξ hξ
    · exact hchain.pairwise_sUnion.mpr (fun S hS => (hc hS).2)
  · intro S hS
    exact Set.subset_sUnion_of_mem hS

/-- Maximality forces density: any nonzero vector in the orthogonal
complement would supply an additional orthogonal cyclic summand. -/
theorem maximal_orthogonalCyclicFamily_dense
    (N : StarSubalgebra ℂ (H →L[ℂ] H)) {S : Set H}
    (hS : Maximal (OrthogonalCyclicFamily N) S) :
    (cyclicFamilySpan N S).topologicalClosure = ⊤ := by
  classical
  let M := (cyclicFamilySpan N S).closure
  change M.toSubmodule = ⊤
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro ξ hξ
  change ξ = 0
  by_contra hne
  have hξold (η : H) (hη : η ∈ S) :
      ξ ∈ (orbitClosure N η).toSubmodule.orthogonal := by
    apply Submodule.orthogonal_le (show (orbitClosure N η).toSubmodule ≤ M.toSubmodule from
      (orbitClosure_le_cyclicFamilySpan N hη).trans (Submodule.le_topologicalClosure _))
    exact hξ
  have hnew (η : H) (hη : η ∈ S) : CyclicOrbitOrthogonal N ξ η := by
    intro x hx y hy
    exact inner_eq_zero_symm.mp (orbitClosure_le_orthogonal N ξ η (hξold η hη) hx y hy)
  have hnot : ξ ∉ S := by
    intro hmem
    exact hne (inner_self_eq_zero.mp (hnew ξ hmem ξ (self_mem_orbitClosure N ξ)
      ξ (self_mem_orbitClosure N ξ)))
  have hins : OrthogonalCyclicFamily N (insert ξ S) := by
    constructor
    · intro η hη
      rcases Set.mem_insert_iff.mp hη with rfl | hη
      · exact hne
      · exact hS.prop.1 η hη
    · intro η hη ζ hζ hηζ
      rcases Set.mem_insert_iff.mp hη with hηeq | hηS
      · rcases Set.mem_insert_iff.mp hζ with hζeq | hζS
        · exact (hηζ (hηeq.trans hζeq.symm)).elim
        · simpa only [hηeq] using hnew ζ hζS
      · rcases Set.mem_insert_iff.mp hζ with hζeq | hζS
        · simpa only [hζeq] using cyclicOrbitOrthogonal_symm N (hnew η hηS)
        · exact hS.prop.2 hηS hζS hηζ
  have heq : S = insert ξ S := hS.eq_of_subset hins (Set.subset_insert ξ S)
  exact hnot (heq.symm ▸ Set.mem_insert ξ S)

/-- A chosen maximal family, together with its proved density. -/
structure CyclicDecompositionData (N : StarSubalgebra ℂ (H →L[ℂ] H)) where
  generators : Set H
  nonzero : ∀ ξ ∈ generators, ξ ≠ 0
  orthogonal : generators.Pairwise (CyclicOrbitOrthogonal N)
  dense_span : (cyclicFamilySpan N generators).topologicalClosure = ⊤

def cyclicDecompositionData (N : StarSubalgebra ℂ (H →L[ℂ] H)) : CyclicDecompositionData N := by
  let S := (exists_maximal_orthogonalCyclicFamily N).choose
  have hS := (exists_maximal_orthogonalCyclicFamily N).choose_spec
  exact ⟨S, hS.prop.1, hS.prop.2, maximal_orthogonalCyclicFamily_dense N hS⟩

namespace CyclicDecompositionData

variable {N : StarSubalgebra ℂ (H →L[ℂ] H)} (D : CyclicDecompositionData N)

abbrev Space (i : D.generators) : Type _ := ↥(orbitClosure N (i : H))

/-- The closed cyclic spaces, as an actual complete orthogonal family. -/
def summands : OrthogonalSummandDecomposition D.Space H where
  inclusion i := (orbitClosure N (i : H)).toSubmodule.subtypeₗᵢ
  orthogonal i j hij x y := by
    exact D.orthogonal i.property j.property (fun h => hij (Subtype.ext h))
      x x.property y y.property
  dense_span := by
    have hset : (⋃ i : D.generators,
        Set.range (orbitClosure N (i : H)).toSubmodule.subtypeₗᵢ) =
        ⋃ ξ ∈ D.generators, (orbitClosure N ξ : Set H) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_range, SetCoe.exists]
      constructor
      · rintro ⟨ξ, hξ, y, rfl⟩
        exact ⟨ξ, hξ, y.property⟩
      · rintro ⟨ξ, hξ, hx⟩
        exact ⟨ξ, hξ, ⟨x, hx⟩, rfl⟩
    change (Submodule.span ℂ _).topologicalClosure = ⊤
    rw [hset]
    exact D.dense_span

end CyclicDecompositionData

variable {A : Type*} [CStarAlgebra A]

/-- The bounded action on the actual closed orbit subspace. -/
def orbitAction (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A) :
    orbitClosure σ.range ξ →L[ℂ] orbitClosure σ.range ξ :=
  (σ a).restrict (orbitClosure_invariant σ.range ξ (σ.rangeRestrict a))

@[simp] theorem orbitAction_coe (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A)
    (x : orbitClosure σ.range ξ) : (orbitAction σ ξ a x : H) = σ a (x : H) := rfl

/-- Restriction to a cyclic reducing subspace is a unital star representation. -/
def orbitRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    A →⋆ₐ[ℂ] (orbitClosure σ.range ξ →L[ℂ] orbitClosure σ.range ξ) where
  toFun := orbitAction σ ξ
  map_zero' := by
    ext x
    simp
  map_one' := by
    ext x
    simp
  map_add' a b := by
    ext x
    simp
  map_mul' a b := by
    ext x
    simp [mul_apply_eq_comp]
  commutes' c := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : H) (σ (star a) (x : H)) =
      inner ℂ y ((orbitAction σ ξ a).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : H) (σ (star a) (x : H)) =
      inner ℂ (σ a (y : H)) (x : H)
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem orbitRepresentation_coe (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A)
    (x : orbitClosure σ.range ξ) : (orbitRepresentation σ ξ a x : H) = σ a (x : H) := rfl

def orbitGenerator (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : orbitClosure σ.range ξ :=
  ⟨ξ, self_mem_orbitClosure σ.range ξ⟩

/-- The original vector has dense orbit for the restricted action. -/
theorem orbitGenerator_dense (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    DenseRange (fun a : A => orbitRepresentation σ ξ a (orbitGenerator σ ξ)) := by
  change Dense (Set.range (fun a : A => orbitRepresentation σ ξ a (orbitGenerator σ ξ)))
  have hset : Set.range (fun a : A => orbitRepresentation σ ξ a (orbitGenerator σ ξ)) =
      Set.range (orbitIntoClosure σ.range ξ) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨σ.rangeRestrict a, rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := a.property
      refine ⟨b, ?_⟩
      apply Subtype.ext
      change σ b ξ = (a : H →L[ℂ] H) ξ
      change σ b = (a : H →L[ℂ] H) at hb
      rw [hb]
  rw [hset]
  exact orbitIntoClosure_dense σ.range ξ

/-- The original vector is a cyclic generator for the restricted action. -/
theorem orbitRepresentation_cyclic (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    CyclicStarRepresentation (orbitRepresentation σ ξ) :=
  ⟨orbitGenerator σ ξ, orbitGenerator_dense σ ξ⟩

namespace CyclicDecompositionData

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData σ.range)

/-- The star representation on each member of the Zorn family. -/
def representation (i : D.generators) : A →⋆ₐ[ℂ] (D.Space i →L[ℂ] D.Space i) :=
  orbitRepresentation σ (i : H)

def generator (i : D.generators) : D.Space i := orbitGenerator σ (i : H)

theorem generator_dense (i : D.generators) :
    DenseRange (fun a : A => D.representation σ i a (D.generator σ i)) :=
  orbitGenerator_dense σ i

theorem representation_cyclic (i : D.generators) :
    CyclicStarRepresentation (D.representation σ i) := orbitRepresentation_cyclic σ i

theorem representation_intertwines (i : D.generators) (a : A) :
    (σ a).comp (D.summands.inclusion i).toContinuousLinearMap =
      (D.summands.inclusion i).toContinuousLinearMap.comp (D.representation σ i a) := by
  ext x
  rfl

theorem representation_generator_nonzero (i : D.generators) : orbitGenerator σ (i : H) ≠ 0 := by
  intro hzero
  exact D.nonzero i i.property (congrArg (fun x : D.Space i => (x : H)) hzero)

end CyclicDecompositionData

end KadisonSimilarity

end

end OAI
