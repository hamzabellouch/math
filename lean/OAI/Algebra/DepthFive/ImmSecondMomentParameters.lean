import OAI.Algebra.DepthFive.ImmCompatibleTrace
import OAI.Algebra.DepthFive.BidegreeLocalProductAverage
import OAI.Algebra.DepthFive.PairingAverageCardinality
import OAI.Algebra.DepthFive.PairingOccupationAverage

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
open Pairings MomentPairing

private theorem source_bound
    (L : ℕ) (side : Fin (L + 1) → Bool)
    [Nonempty {x : Fin (L + 1) × (Fin (L + 1) × Fin (L + 1)) // side x.1 = true}]
    [Nonempty {x : Fin (L + 1) × (Fin (L + 1) × Fin (L + 1)) // ¬ side x.1 = true}]
    (a b : ℕ) (ha : 0 < a) :
    (∑ M : ImmSourceIndex (L + 1) side a b,
      ∑ x : {x : Fin L → Labels (Fin (L + 1)) // Compatible 0 x},
        ∏ t : Fin (L + 1), LocalMoments.localPolynomial (side t)
          (fun y => M.1 (t, y)) (MomentPairing.layerLabels 0 x.1 t).p
            (MomentPairing.layerLabels 0 x.1 t).q (MomentPairing.layerLabels 0 x.1 t).r) ≤
      (Fintype.card (ImmSourceIndex (L + 1) side a b) : ℝ) *
        pathMean side (layerMeanV (Fin (L + 1)) side a)
          (layerMeanU (Fin (L + 1)) side b) ^ 2 *
        ∑ τ : Fin (L + 1) → Kind,
          ∑ x : RelaxedPaths (Fin (L + 1)) 0 τ,
            pathWeight side
              (layerMeanV (Fin (L + 1)) side a /
                (layerMeanV (Fin (L + 1)) side a + 1))
              (layerMeanU (Fin (L + 1)) side b /
                (layerMeanU (Fin (L + 1)) side b + 1)) 0 τ x.1 := by
  classical
  have hA : 0 < layerMeanV (Fin (L + 1)) side a := by
    unfold layerMeanV
    exact div_pos (by exact_mod_cast ha) (by exact_mod_cast Fintype.card_pos)
  have hB : 0 ≤ layerMeanU (Fin (L + 1)) side b := by
    unfold layerMeanU
    positivity
  apply sum_sources_local_moments_le_of_average
    (ι := ImmSourceIndex (L + 1) side a b) (γ := Fin (L + 1)) (L := L) side hA hB 0
    (fun M : ImmSourceIndex (L + 1) side a b => fun x =>
      ∏ t : Fin (L + 1), LocalMoments.localPolynomial (side t)
        (fun y => M.1 (t, y)) (MomentPairing.layerLabels 0 x t).p
          (MomentPairing.layerLabels 0 x t).q (MomentPairing.layerLabels 0 x t).r)
  intro x _
  simpa only [layerMeanV, layerMeanU] using
    LocalMoments.bidegree_average_layered_localProduct_le side a b Finset.univ
      (fun t => (MomentPairing.layerLabels 0 x t).p) (fun t => (MomentPairing.layerLabels 0 x t).q)
      (fun t => (MomentPairing.layerLabels 0 x t).r)

/-- The actual finite IMM second trace is bounded by the relaxed pairing sum,
with precisely one source dimension and the square of the path mean. -/
theorem immNormalizedMatrix_second_moment_le_relaxed
    (L : ℕ) (side : Fin (L + 1) → Bool)
    [Nonempty {x : Fin (L + 1) × (Fin (L + 1) × Fin (L + 1)) // side x.1 = true}]
    [Nonempty {x : Fin (L + 1) × (Fin (L + 1) × Fin (L + 1)) // ¬ side x.1 = true}]
    (a b : ℕ) (ha : 0 < a) :
    let A := immNormalizedMatrix (L + 1) side a b
    ((A.conjTranspose * A) ^ 2).trace.re ≤
      (Fintype.card (ImmSourceIndex (L + 1) side a b) : ℝ) *
        pathMean side (layerMeanV (Fin (L + 1)) side a)
          (layerMeanU (Fin (L + 1)) side b) ^ 2 *
        ∑ τ : Fin (L + 1) → Kind,
          ∑ x : RelaxedPaths (Fin (L + 1)) 0 τ,
            pathWeight side
              (layerMeanV (Fin (L + 1)) side a /
                (layerMeanV (Fin (L + 1)) side a + 1))
              (layerMeanU (Fin (L + 1)) side b /
                (layerMeanU (Fin (L + 1)) side b + 1)) 0 τ x.1 := by
  exact (immNormalizedMatrix_second_trace_le_compatible L side a b).trans
    (source_bound L side a b ha)

end Problem335

end

end OAI
