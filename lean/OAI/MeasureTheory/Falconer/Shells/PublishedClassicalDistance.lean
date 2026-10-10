import OAI.MeasureTheory.Falconer.Measures.FrostmanDimension

namespace OAI

/-! # The published strict classical threshold, only for compact sets

Mattila–Sjölin, *Regularity of Distance Measures and Sets*, Mathematische
Nachrichten 204 (1999), 157–162, DOI 10.1002/mana.19992040110.
The corollary stated in the publisher's abstract says that a Suslin set in
R^n of Hausdorff dimension greater than (n+1)/2 has a distance set with
nonempty interior. Here only its weaker compact positive-measure
specialization is used.

https://onlinelibrary.wiley.com/doi/abs/10.1002/mana.19992040110
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

def PublishedClassicalDistance : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ K : Set (Space n), IsCompact K →
    ENNReal.ofReal (((n:ℝ)+1)/2) < dimH K → 0 < volume (distanceSet K)

theorem classical_distance_of_frostman (hpublished : PublishedClassicalDistance)
    {n : ℕ} (hn : 2 ≤ n) (μ : ProbabilityMeasure (Space n))
    (hK : IsCompact (μ : Measure (Space n)).support) {s C : ℝ}
    (hs : ((n:ℝ)+1)/2 < s) (hC : 0 < C)
    (hfrost : FrostmanBallBound (μ : Measure (Space n)) s C) :
    0 < volume (distanceSet (μ : Measure (Space n)).support) := by
  have hs0 : 0 < s := (by positivity : (0:ℝ) ≤ ((n:ℝ)+1)/2).trans_lt hs
  apply hpublished n hn _ hK
  exact ((ENNReal.ofReal_lt_ofReal_iff hs0).mpr hs).trans_le
    (frostman_dimension_lower μ hs0 hC hfrost)

end Falconer

end OAI
