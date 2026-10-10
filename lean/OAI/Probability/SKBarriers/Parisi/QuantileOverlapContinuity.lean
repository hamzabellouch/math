import Mathlib
import OAI.Probability.SKBarriers.Scalar.PartitionOverlapContinuity
import OAI.Probability.SKBarriers.Parisi.QuantileCDFOverlap

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOverlap_continuousOn_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q ∈ admissibleQuantiles k) :
    ContinuousOn (scalarCDFOverlap β (quantileCDF k Q)) (Icc (0:ℝ) 1) := by
  let q := Fin.snoc (α := fun _ => ℝ) (Fin.cons (α := fun _ => ℝ) 0 Q) (1:ℝ)
  let m := Fin.snoc (α := fun _ => ℝ) (quantileMass k) (1:ℝ)
  have hq : Monotone q := monotone_snoc_one _
    (monotone_cons_zero_quantiles Q hQ.1 (hQ.2 0).1) (by simpa using (hQ.2 (Fin.last k)).2)
  have hq0 : q 0=0 := by simp [q]
  have hq1 : q (Fin.last (k+2))=1 := by simp [q]
  have hm (i : Fin (k+2)) : m i ∈ Icc (0:ℝ) 1 := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [m]
    · simpa [m] using quantileMass_bounds k i
  have hmodel (i : Fin (k+2)) (z : ℝ) (hz : z ∈ Ico (q i.castSucc) (q i.succ)) :
      quantileCDF k Q z=m i := by
    revert hz
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hz
      simp only [m,Fin.snoc_last]

      apply quantileCDF_of_last_le Q hQ.1
      simpa [q] using hz.1
    · intro hz
      simpa [m] using quantileCDF_on_interval Q hQ.1 i z (by simpa only [q,← Fin.castSucc_succ,Fin.snoc_castSucc,Fin.cons_succ] using hz)
  exact scalarCDFOverlap_continuousOn_partition β (quantileCDF_bounds k Q)
    (quantileCDF_monotone k Q) (k+2) q hq hq0 hq1 m hm hmodel

end SK.Analytic

end
end

end OAI
