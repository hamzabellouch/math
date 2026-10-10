import OAI.MeasureTheory.SelfSimilar.UnweightedAttractor

namespace OAI

universe uι

open scoped BigOperators ENNReal

namespace CorSetReference

section
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

/-- All infinite addresses, not an almost-everywhere image. -/
noncomputable def codingPoint (r t : ι → ℝ) (ω : ℕ → ι) : ℝ :=
  ∑' n, (∏ j ∈ Finset.range n, r (ω j)) * t (ω n)

/-- The manuscript explicitly identifies its compact attractor with coding limits. -/
noncomputable def attractor (r t : ι → ℝ) : Set ℝ :=
  Set.range (codingPoint r t)

/-- Full affine coefficients of the composition in address order. -/
def word (r t : ι → ℝ) : List ι → ℝ × ℝ :=
  List.foldr (fun symbol coefficients =>
    (r symbol * coefficients.1, r symbol * coefficients.2 + t symbol)) (1, 0)

end

open EntropyRateDimension EntropyRateDimension.Extensions

/-- The compact coding attractor and its similarity and Hausdorff dimensions. -/
theorem cor_set {ι : Type uι} [Fintype ι] [Nonempty ι]
    (r t : ι → ℝ) (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1)
    (hno : ∀ u v : List ι, u ≠ [] → v ≠ [] →
      word r t u = word r t v → u = v) :
    IsCompact (attractor r t) ∧ (attractor r t).Nonempty ∧
    (∃! s : ℝ, 0 ≤ s ∧ ∑ i, |r i| ^ s = 1) ∧
    (∀ s : ℝ, 0 ≤ s → (∑ i, |r i| ^ s = 1) →
      dimH (attractor r t) = ENNReal.ofReal (min 1 s)) := by
  have hword (w : List ι) :
      (uniformSystem r t hr0 hr1).wordAffine w = word r t w := by
    induction w with
    | nil => rfl
    | cons i w ih =>
      change (r i * ((uniformSystem r t hr0 hr1).wordAffine w).1,
        r i * ((uniformSystem r t hr0 hr1).wordAffine w).2 + t i) =
        (r i * (word r t w).1, r i * (word r t w).2 + t i)
      rw [ih]
  have hno' : ∀ u v : List ι, u ≠ [] → v ≠ [] →
      (uniformSystem r t hr0 hr1).wordAffine u =
        (uniformSystem r t hr0 hr1).wordAffine v → u = v := by
    intro u v hu hv he
    apply hno u v hu hv
    simpa only [hword] using he
  refine ⟨?_, ?_, unweighted_existsUnique_similarityDimension r t hr0 hr1, ?_⟩
  · exact unweightedAttractor_compact r t hr0 hr1
  · exact Set.range_nonempty _
  · intro a ha he
    exact unweighted_no_exact_overlaps_attractor_dimension_of_root r t hr0 hr1 a ha he hno'

end CorSetReference

end OAI
