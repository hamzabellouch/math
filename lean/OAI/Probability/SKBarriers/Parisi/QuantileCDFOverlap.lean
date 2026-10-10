import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarMomentShift
import OAI.Probability.SKBarriers.Scalar.PartitionOverlapIndex
import OAI.Probability.SKBarriers.Parisi.CDFAtomicRepresentation

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantileMass_bounds (k : ℕ) (i : Fin (k+1)) :
    quantileMass k i ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (by positivity : (0:ℝ)<(k+1:ℕ))).mpr
    exact_mod_cast i.isLt.le

theorem monotone_snoc_one {n : ℕ} (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (h1 : q (Fin.last n) ≤ 1) : Monotone (Fin.snoc q (1:ℝ)) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using h1
  · simpa only [← Fin.castSucc_succ,Fin.snoc_castSucc] using hq (Fin.castSucc_le_succ j)

theorem scalarCDFOverlap_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q ∈ admissibleQuantiles k) (j : Fin (k+1)) :
    scalarCDFOverlap β (quantileCDF k Q) (Q j)=quantileOverlapMean k β Q j := by
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
  have H := scalarCDFOverlap_eq_partition_index β (quantileCDF_bounds k Q)
    (quantileCDF_monotone k Q) (k+2) q hq hq0 hq1 m hm hmodel j.succ.castSucc
  have hj : q j.succ.castSucc=Q j := by simp only [q,Fin.snoc_castSucc,Fin.cons_succ]
  rw [hj] at H
  rw [H,quantileOverlapMean_eq_scalar]
  rw [scalarMomentSquare,Fin.lastCases_castSucc]
  have hv : (fun i : Fin (k+1) => timeGridCoefficients (k+2) β q i.castSucc)=
      fun i => β*Real.sqrt (cumulativeGapMap k Q i) := by
    funext i
    simp only [timeGridCoefficients,q,← Fin.castSucc_succ,Fin.snoc_castSucc]
    rw [quantile_knots_gap]
  have hm' : (fun i : Fin (k+1) => m i.castSucc)=quantileMass k := by funext i; simp [m]
  rw [hm',hv]
  simp only [m,Fin.snoc_last,scalarStep_one_spin,scalarStepAverage_one_spin]
  exact congrFun (scalarMomentSquare_add_const (k+1) (quantileMass k)
    (fun i => β*Real.sqrt (cumulativeGapMap k Q i)) scalarSpinTerminal_regular
    scalarMagnetization _ j.succ) 0

end SK.Analytic

end
end

end OAI
