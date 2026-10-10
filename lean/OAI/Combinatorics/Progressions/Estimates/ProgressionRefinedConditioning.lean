import OAI.Combinatorics.Progressions.Lattices.ResidueRefinementBudgets

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def progressionRefinedCubeEmbedding (q m H : ℕ) (c : ℤ) (hm : 0 < m)
    (P : Set ℤ) (hP : (integerProgressionSupport c (m : ℤ) H : Set ℤ) ⊆ P)
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, m ∣ n i)
    (r : (progressionCubeSlice q m H c).ResidueLabel n) :
    ((progressionCubeSlice q m H c).refineResidues n r).Domain ↪ SupportedCube q P :=
  ((progressionCubeSlice q m H c).refineResiduesEmbedding n hdvd r).trans
    (progressionCubeSliceEmbedding q m H c hm P hP)

theorem progressionRefinedCubeEmbedding_coordinates (q m H : ℕ) (c : ℤ) (hm : 0 < m)
    (P : Set ℤ) (hP : (integerProgressionSupport c (m : ℤ) H : Set ℤ) ⊆ P)
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, m ∣ n i)
    (r : (progressionCubeSlice q m H c).ResidueLabel n)
    (x : ((progressionCubeSlice q m H c).refineResidues n r).Domain) :
    supportedCubeCoordinates (progressionRefinedCubeEmbedding q m H c hm P hP n hdvd r x).val =
      ((progressionCubeSlice q m H c).refineResidues n r).coordinates x := rfl

theorem progressionRefinedCubeEmbedding_range (q m H : ℕ) (c : ℤ) (hm : 0 < m)
    (P : Set ℤ) [Finite P] (hP : (integerProgressionSupport c (m : ℤ) H : Set ℤ) ⊆ P)
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, m ∣ n i)
    (r : (progressionCubeSlice q m H c).ResidueLabel n) :
    finiteEmbeddingRange (progressionRefinedCubeEmbedding q m H c hm P hP n hdvd r) =
      Finset.univ.filter (fun x =>
        (∀ ω : Fin q → Bool, x.val.2 + cubeShift x.val.1 ω ∈ integerProgressionSupport c (m : ℤ) H) ∧
        ∀ i, (supportedCubeCoordinates x.val i : ZMod (n i)) = r.val i) := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
    subst x
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, y.property⟩
    exact ((progressionResidueSupportedCubeEquiv q m H c hm).symm
      ((progressionCubeSlice q m H c).refineResiduesEmbedding n hdvd r y)).property
  · intro hx
    obtain ⟨hvertices, hres⟩ := (Finset.mem_filter.mp hx).2
    let y : SupportedCube q (integerProgressionSupport c (m : ℤ) H : Set ℤ) := ⟨x.val, hvertices⟩
    let z := progressionResidueSupportedCubeEquiv q m H c hm y
    let t : ((progressionCubeSlice q m H c).refineResidues n r).Domain := ⟨z.val, hres⟩
    exact Finset.mem_map.mpr ⟨t, Finset.mem_univ t, Subtype.ext rfl⟩

theorem progressionRefinedCube_condition_complexMean (q m H : ℕ) (c : ℤ) (hm : 0 < m)
    (P : Set ℤ) [Finite P] (hP : (integerProgressionSupport c (m : ℤ) H : Set ℤ) ⊆ P)
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, m ∣ n i)
    (r : (progressionCubeSlice q m H c).ResidueLabel n)
    (w : (Option (Fin q) → ℤ) → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hmass : 0 < ∑ x : ((progressionCubeSlice q m H c).refineResidues n r).Domain,
      w (((progressionCubeSlice q m H c).refineResidues n r).coordinates x))
    (f : (Option (Fin q) → ℤ) → ℂ) :
    (FiniteProbabilityWeights.conditionAlongEmbedding
      (fun x : SupportedCube q P => w (supportedCubeCoordinates x.val))
      (fun x => hw (supportedCubeCoordinates x.val))
      (progressionRefinedCubeEmbedding q m H c hm P hP n hdvd r) hmass).complexMean
        (fun x => f (supportedCubeCoordinates x.val)) =
      (FiniteProbabilityWeights.ofPositiveWeights
        (fun x : ((progressionCubeSlice q m H c).refineResidues n r).Domain =>
          w (((progressionCubeSlice q m H c).refineResidues n r).coordinates x))
        (fun x => hw (((progressionCubeSlice q m H c).refineResidues n r).coordinates x)) hmass).complexMean
        (fun x => f (((progressionCubeSlice q m H c).refineResidues n r).coordinates x)) :=
  FiniteProbabilityWeights.conditionAlongEmbedding_complexMean _ _
    (progressionRefinedCubeEmbedding q m H c hm P hP n hdvd r) hmass _

end Erdos3

end

end OAI
