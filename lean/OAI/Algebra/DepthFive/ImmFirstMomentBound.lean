import OAI.Algebra.DepthFive.ImmFirstTrace
import OAI.Algebra.DepthFive.PathMassLowerBound

namespace OAI

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

/-- The independent geometric benchmark for one IMM path. -/
def immFirstMomentMean (n : ℕ) (side : Fin n → Bool) (a b : ℕ) : ℝ :=
  ((a : ℝ) / Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = true}) ^
      immLayerVCount side *
    (1 + (b : ℝ) / Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = false}) ^
      immLayerUCount side

/-- The explicit finite-size occupation loss, before parameter specialization. -/
def immFirstMomentLoss (n : ℕ) (side : Fin n → Bool) (a b : ℕ) : ℝ :=
  (immLayerVCount side : ℝ) ^ 2 / a +
    (immLayerVCount side : ℝ) ^ 2 /
      (2 * Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = true}) +
    (immLayerUCount side : ℝ) ^ 2 / b +
    (immLayerUCount side : ℝ) ^ 2 /
      (2 * Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = false})

/-- First-moment lower bound for the actual finite normalized IMM matrix.
The only hypotheses are positive occupation totals, nonempty variable groups,
and the elementary order range required by the occupation ratio estimate. -/
theorem immNormalizedMatrix_first_moment_lower
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ)
    [Nonempty {x : Fin n × Fin n × Fin n // side x.1 = true}]
    [Nonempty {x : Fin n × Fin n × Fin n // side x.1 = false}]
    (ha : 0 < a) (hb : 0 < b)
    (hk : 2 * immLayerVCount side ≤ a) (hm : 2 * immLayerUCount side ≤ b) :
    (Fintype.card (ImmSourceIndex n side a b) : ℝ) * (n : ℝ) ^ (n - 1) *
        (Real.exp (-immFirstMomentLoss n side a b) * immFirstMomentMean n side a b) ≤
      ((immNormalizedMatrix n side a b).conjTranspose *
        immNormalizedMatrix n side a b).trace.re := by
  classical
  apply immNormalizedMatrix_first_trace_lower_of_average n hn side a b
  intro p
  have h := immPath_source_mass_lower n hn side a b ((immPaths n hn).get p)
    (List.get_mem _ p) ha hb hk hm
  change _ ≤ (∑ d : ImmSourceIndex n side a b,
    immPathAmplitude n hn (fun x => side x.1) d.1 p ^ 2) /
      (Fintype.card (ImmSourceIndex n side a b) : ℝ) at h
  convert h using 1
  apply congrArg₂ (fun x y : ℝ => x * y)
  · apply congrArg Real.exp
    dsimp [immFirstMomentLoss, immLayerVCount, immLayerUCount]
    ring
  · rfl

end Problem335

end

end OAI
