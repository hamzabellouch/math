import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarOverlapContinuity
import OAI.Probability.SKBarriers.Replicas.TwoPartitionOverlap

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOverlap_continuousOn_partition (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (hq1 : q (Fin.last n)=1)
    (m : Fin n → ℝ) (hm : ∀ i, m i∈Icc (0:ℝ) 1)
    (hmodel : ∀ i : Fin n, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i) :
    ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1) := by
  let v : ℝ → Fin (n+n) → ℝ := fun r =>
    Fin.append (timeGridCoefficients n β (fun i => min (q i) r))
      (timeGridCoefficients n β (fun i => max (q i) r))
  have hc : Continuous v := by
    apply continuous_pi
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [v,Fin.append_left,timeGridCoefficients]
      fun_prop
    · intro j
      simp only [v,Fin.append_right,timeGridCoefficients]
      fun_prop
  have H := (scalarMomentSquare_contDiff_coeff (n+n) (Fin.append m m) ⟨n,by omega⟩).continuous.comp hc
  apply H.continuousOn.congr
  intro r hr
  have hpre (i : Fin n) (z : ℝ) (hz : z∈Ico (min (q i.castSucc) r) (min (q i.succ) r)) :
      α z=m i := by
    apply hmodel i z
    constructor
    · rcases min_le_iff.mp hz.1 with h|h
      · exact h
      · exact False.elim (not_lt_of_ge h (lt_min_iff.mp hz.2).2)
    · exact (lt_min_iff.mp hz.2).1
  have hpost (i : Fin n) (z : ℝ) (hz : z∈Ico (max (q i.castSucc) r) (max (q i.succ) r)) :
      α z=m i := by
    apply hmodel i z
    constructor
    · exact (le_max_left _ _).trans hz.1
    · rcases lt_max_iff.mp hz.2 with h|h
      · exact h
      · exact False.elim (not_lt_of_ge ((le_max_right _ _).trans hz.1) h)
  have H' := scalarCDFOverlap_eq_two_partitions β hα hαm n n
    (fun i => min (q i) r) (fun i => max (q i) r)
    (by intro i j hij; exact min_le_min (hq hij) le_rfl)
    (by intro i j hij; exact max_le_max (hq hij) le_rfl)
    (by simp only [hq0,min_eq_left hr.1])
    (by simp only [hq1,max_eq_left hr.2])
    (by simp only [hq1,hq0,min_eq_right hr.2,max_eq_right hr.1])
    m m hm hm hpre hpost
  simpa only [hq0,max_eq_right hr.1,Function.comp_def,v] using H'

end SK.Analytic

end
end

end OAI
