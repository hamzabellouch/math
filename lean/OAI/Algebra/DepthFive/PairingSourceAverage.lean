import OAI.Algebra.DepthFive.BidegreeLocalProductAverage
import OAI.Algebra.DepthFive.PairingOccupationAverage
import OAI.Algebra.DepthFive.PairingAverageCardinality

namespace OAI

/-! The canonical finite source sum enters the normalized relaxed pairing bound
with exactly one source dimension and no assumed occupation estimate. -/

noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing
open Pairings

variable {γ : Type*} [Fintype γ] [DecidableEq γ] {L : ℕ}

theorem bidegree_source_average_eq_occupationPathMean
    (side : Fin (L + 1) → Bool) (a b : ℕ)
    [Fintype {d : (Fin (L + 1) × (γ × γ)) →₀ ℕ //
      Finsupp.weight (bidegreeWeight (fun v => side v.1)) d = (a, b)}]
    (endpoint : γ) (x : Fin L → Labels γ) :
    (∑ d : {d : (Fin (L + 1) × (γ × γ)) →₀ ℕ //
        Finsupp.weight (bidegreeWeight (fun v => side v.1)) d = (a, b)},
      ∏ t, LocalMoments.localPolynomial (side t) (fun y => d.val (t, y))
        (layerLabels endpoint x t).p (layerLabels endpoint x t).q
        (layerLabels endpoint x t).r) /
      (Fintype.card {d : (Fin (L + 1) × (γ × γ)) →₀ ℕ //
        Finsupp.weight (bidegreeWeight (fun v => side v.1)) d = (a, b)} : ℝ) =
      occupationPathMean side a b endpoint x := by
  exact bidegree_average_eq_partitionCompositionMean
    (fun v : Fin (L + 1) × (γ × γ) => side v.1) a b
    (fun M => ∏ t, LocalMoments.localPolynomial (side t) (fun y => M (t, y))
      (layerLabels endpoint x t).p (layerLabels endpoint x t).q
      (layerLabels endpoint x t).r)

/-- Concrete source reindexing, finite occupation comparison, normalization,
and relaxation. In particular, the source cardinality occurs only once. -/
theorem sum_bidegree_source_local_moments_le
    (side : Fin (L + 1) → Bool)
    [Nonempty {v : Fin (L + 1) × (γ × γ) // side v.1 = true}]
    [Nonempty {v : Fin (L + 1) × (γ × γ) // ¬ side v.1 = true}]
    (a b : ℕ) (ha : 0 < a)
    [Fintype {d : (Fin (L + 1) × (γ × γ)) →₀ ℕ //
      Finsupp.weight (bidegreeWeight (fun v => side v.1)) d = (a, b)}]
    (endpoint : γ) :
    (∑ d : {d : (Fin (L + 1) × (γ × γ)) →₀ ℕ //
        Finsupp.weight (bidegreeWeight (fun v => side v.1)) d = (a, b)},
      ∑ x : {x : Fin L → Labels γ // Compatible endpoint x},
        ∏ t, LocalMoments.localPolynomial (side t) (fun y => d.val (t, y))
          (layerLabels endpoint x.1 t).p (layerLabels endpoint x.1 t).q
          (layerLabels endpoint x.1 t).r) ≤
      (Fintype.card {d : (Fin (L + 1) × (γ × γ)) →₀ ℕ //
        Finsupp.weight (bidegreeWeight (fun v => side v.1)) d = (a, b)} : ℝ) *
      pathMean side (layerMeanV γ side a) (layerMeanU γ side b) ^ 2 *
      ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
        pathWeight side
          (layerMeanV γ side a / (layerMeanV γ side a + 1))
          (layerMeanU γ side b / (layerMeanU γ side b + 1)) endpoint τ x.1 := by
  have hA : 0 < layerMeanV γ side a := by
    unfold layerMeanV
    exact div_pos (by exact_mod_cast ha) (by exact_mod_cast Fintype.card_pos)
  have hB : 0 ≤ layerMeanU γ side b := by
    unfold layerMeanU
    positivity
  apply sum_sources_local_moments_le_of_average
    (ι := {d : (Fin (L + 1) × (γ × γ)) →₀ ℕ //
      Finsupp.weight (bidegreeWeight (fun v => side v.1)) d = (a, b)})
    side hA hB endpoint
    (fun d x => ∏ t, LocalMoments.localPolynomial (side t) (fun y => d.val (t, y))
      (layerLabels endpoint x t).p (layerLabels endpoint x t).q
      (layerLabels endpoint x t).r)
  intro x hx
  have h := LocalMoments.bidegree_average_layered_localProduct_le side a b
    Finset.univ (fun t => (layerLabels endpoint x t).p)
      (fun t => (layerLabels endpoint x t).q) (fun t => (layerLabels endpoint x t).r)
  simpa [layerMeanV, layerMeanU] using h

end Problem335.MomentPairing

end

end OAI
