import OAI.Probability.FreeIsing.Ising.LogWeightedOrbitCut
import OAI.Probability.FreeIsing.Trees.PathReverseRerooting

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyPathBounds ConnectedHull

def edge {d : ℕ} (inward : Bool) (v : TreeVertex d) (i : ℕ) :
    TreeVertex d × TreeVertex d :=
  if inward then (takeVertex v i, takeVertex v (i + 1))
  else (takeVertex v (i + 1), takeVertex v i)

def attenuation {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta) (t : ℝ≥0)
    (inward : Bool) (v : TreeVertex d) (x : Paths d) : ℝ :=
  ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
    (cavityObservable hb t (edge inward v i).1 (edge inward v i).2 x)

def logSum {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta) (t : ℝ≥0)
    (inward : Bool) (v : TreeVertex d) (s : Finset ℕ) :
    IsingConditionalCopyBounds.CopySpace d → ℝ :=
  pathLogDifference hb t s (edge inward v)

theorem measurable_attenuation {d : ℕ} {beta : ℝ}
    (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) :
    Measurable (attenuation hb t inward v) := by
  unfold attenuation
  exact Finset.measurable_prod _ (fun i _ =>
    (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).measurable.comp
      (measurable_cavityObservable hb t _ _))

theorem attenuation_mem_Icc {d : ℕ} {beta : ℝ}
    (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) (x : Paths d) :
    0 ≤ attenuation hb t inward v x ∧ attenuation hb t inward v x ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i _ =>
      (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le)
  · exact Finset.prod_le_one₀
      (fun i _ => (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le)
      (fun i _ => responseAttenuation_le_one (Real.tanh_sq_lt_one beta).le _)

@[simp] theorem attenuation_outward {d : ℕ} {beta : ℝ}
    (hb : 0 ≤ beta) (t : ℝ≥0) (v : TreeVertex d) :
    attenuation hb t false v = IsingRootAttenuation.rootAttenuation hb t v := rfl

end Problem367.IsingOrientedPath

end

end OAI
