import Mathlib
import OAI.Probability.SKBarriers.Scalar.PartitionOverlap
import OAI.Probability.SKBarriers.Parisi.QuantileScalarOverlap

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOverlap_eq_partition_index (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (hq1 : q (Fin.last n)=1)
    (m : Fin n → ℝ) (hm : ∀ i, m i∈Icc (0:ℝ) 1)
    (hmodel : ∀ i : Fin n, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i)
    (j : Fin (n+1)) :
    scalarCDFOverlap β α (q j)=
      scalarMomentSquare n m (timeGridCoefficients n β q) scalarSpinTerminal scalarMagnetization j 0 := by
  let a := j.1
  let b := n-a
  have hn : a+b=n := Nat.add_sub_of_le (Nat.le_of_lt_succ j.isLt)
  let q' : Fin (a+b+1) → ℝ := fun i => q (Fin.cast (congrArg (·+1) hn) i)
  let m' : Fin (a+b) → ℝ := fun i => m (Fin.cast hn i)
  have hq' : Monotone q' := fun i l hil => hq hil
  have h0 : q' 0=0 := by simpa [q'] using hq0
  have h1 : q' (Fin.last (a+b))=1 := by simpa [q'] using hq1
  have hm' (i : Fin (a+b)) : m' i∈Icc (0:ℝ) 1 := hm _
  have hmodel' (i : Fin (a+b)) (z : ℝ) (hz : z∈Ico (q' i.castSucc) (q' i.succ)) : α z=m' i :=
    hmodel (Fin.cast hn i) z hz
  have H := scalarCDFOverlap_eq_partition β hα hαm a b q' hq' h0 h1 m' hm' hmodel'
  have heq : q' ⟨a,by omega⟩=q j := by congr 1
  rw [heq] at H
  have hv : timeGridCoefficients (a+b) β q'=
      fun i => timeGridCoefficients n β q (Fin.cast hn i) := rfl
  rw [hv] at H
  have hj : (⟨a,by omega⟩:Fin (a+b+1))=Fin.cast (congrArg (·+1) hn.symm) j := by ext; rfl
  rw [hj] at H
  exact H.trans (scalarMomentSquare_cast hn m (timeGridCoefficients n β q)
    scalarSpinTerminal scalarMagnetization j 0)

end SK.Analytic

end
end

end OAI
