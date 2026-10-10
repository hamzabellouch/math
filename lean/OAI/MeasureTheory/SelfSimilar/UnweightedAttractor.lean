import OAI.MeasureTheory.SelfSimilar.AttractorDimension

namespace OAI

universe uι

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι] [Nonempty ι]

/-- Every nonempty finite family of strict nonzero similarities admits positive
normalized weights. The uniform choice is bookkeeping, not a geometric hypothesis. -/
noncomputable def uniformSystem (r t : ι → ℝ)
    (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1) : System ι where
  ratio := r
  offset := t
  weight := fun _ => 1 / (Fintype.card ι : ℝ)
  ratio_pos := hr0
  ratio_lt_one := hr1
  weight_pos := fun _ => one_div_pos.mpr (by exact_mod_cast Fintype.card_pos (α := ι))
  weight_sum := by
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := ι)).ne'
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn

/-- Literal set of all coding limits for the unweighted similarity family. -/
def unweightedAttractor (r t : ι → ℝ)
    (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1) : Set ℝ :=
  Set.range (Coding.point (uniformSystem r t hr0 hr1))

theorem unweightedAttractor_compact (r t : ι → ℝ)
    (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1) :
    IsCompact (unweightedAttractor r t hr0 hr1) :=
  attractor_compact (uniformSystem r t hr0 hr1)

/-- The similarity exponent exists uniquely even for a one-symbol family. -/
theorem unweighted_existsUnique_similarityDimension (r t : ι → ℝ)
    (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1) :
    ∃! s : ℝ, 0 ≤ s ∧ ∑ i, |r i| ^ s = 1 := by
  simpa only [similaritySum, uniformSystem] using
    existsUnique_similarityDimension (uniformSystem r t hr0 hr1)

/-- Source `cor:set` for arbitrary unweighted finite similarities. The overlap
hypothesis uses the manuscript's distinct nonempty finite-word convention, and
the exponent is characterized by its literal normalization equation. -/
theorem unweighted_no_exact_overlaps_attractor_dimension_of_root
    (r t : ι → ℝ) (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1)
    (s : ℝ) (hs : 0 ≤ s) (hroot : ∑ i, |r i| ^ s = 1)
    (hno : ∀ u v : List ι, u ≠ [] → v ≠ [] →
      (uniformSystem r t hr0 hr1).wordAffine u =
        (uniformSystem r t hr0 hr1).wordAffine v → u = v) :
    dimH (unweightedAttractor r t hr0 hr1) = ENNReal.ofReal (min 1 s) := by
  exact no_exact_overlaps_attractor_dimension_of_root (uniformSystem r t hr0 hr1)
    hs hroot ((noExactOverlaps_iff_nonempty (uniformSystem r t hr0 hr1)).mpr hno)

/-- The same statement with the uniquely selected similarity exponent. -/
theorem unweighted_no_exact_overlaps_attractor_dimension
    (r t : ι → ℝ) (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1)
    (hno : ∀ u v : List ι, u ≠ [] → v ≠ [] →
      (uniformSystem r t hr0 hr1).wordAffine u =
        (uniformSystem r t hr0 hr1).wordAffine v → u = v) :
    dimH (unweightedAttractor r t hr0 hr1) =
      ENNReal.ofReal (min 1 (similarityDimension (uniformSystem r t hr0 hr1))) := by
  exact no_exact_overlaps_attractor_dimension (uniformSystem r t hr0 hr1)
    ((noExactOverlaps_iff_nonempty (uniformSystem r t hr0 hr1)).mpr hno)

/-- Unweighted source `lem:overlap-lengths`; no probability data are inputs. -/
theorem unweighted_overlap_lengths
    (r t : ι → ℝ) (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1)
    {u v : List ι} (hu : u ≠ []) (hv : v ≠ []) (hne : u ≠ v)
    (he : (uniformSystem r t hr0 hr1).wordAffine u =
      (uniformSystem r t hr0 hr1).wordAffine v) :
    ∃ a b : List ι, a ≠ [] ∧ b ≠ [] ∧ a.length = b.length ∧ a ≠ b ∧
      (uniformSystem r t hr0 hr1).wordAffine a =
        (uniformSystem r t hr0 hr1).wordAffine b :=
  overlap_lengths (uniformSystem r t hr0 hr1) hu hv hne he

end EntropyRateDimension.Extensions

end OAI
