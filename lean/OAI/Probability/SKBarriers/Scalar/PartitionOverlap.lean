import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarSplit
import OAI.Probability.SKBarriers.Parisi.CDFOverlap
import OAI.Probability.SKBarriers.Parisi.CDFPartitionRepresentation

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def gridPrefix (a b : ℕ) (q : Fin (a+b+1) → ℝ) (i : Fin (a+1)) : ℝ :=
  q ⟨i.1, by omega⟩
def gridSuffix (a b : ℕ) (q : Fin (a+b+1) → ℝ) (i : Fin (b+1)) : ℝ :=
  q ⟨a+i.1, by omega⟩

theorem gridPrefix_monotone {a b : ℕ} {q : Fin (a+b+1) → ℝ}
    (h : Monotone q) : Monotone (gridPrefix a b q) := by
  intro i j hij
  exact h (show (⟨i.1,by omega⟩:Fin (a+b+1)) ≤ ⟨j.1,by omega⟩ from hij)
theorem gridSuffix_monotone {a b : ℕ} {q : Fin (a+b+1) → ℝ}
    (h : Monotone q) : Monotone (gridSuffix a b q) := by
  intro i j hij
  apply h
  exact Nat.add_le_add_left hij a

theorem scalarCDFOverlap_eq_partition (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (a b : ℕ) (q : Fin (a+b+1) → ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (hq1 : q (Fin.last (a+b))=1)
    (m : Fin (a+b) → ℝ) (hm : ∀ i, m i∈Icc (0:ℝ) 1)
    (hmodel : ∀ i : Fin (a+b), ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i) :
    scalarCDFOverlap β α (q ⟨a,by omega⟩)=
      scalarMomentSquare (a+b) m (timeGridCoefficients (a+b) β q)
        scalarSpinTerminal scalarMagnetization ⟨a,by omega⟩ 0 := by
  let r := q ⟨a,by omega⟩
  have hr : r∈Icc (0:ℝ) 1 := by
    constructor
    · rw [← hq0]; exact hq (Fin.zero_le _)
    · rw [← hq1]; exact hq (Fin.le_last _)
  let t := Real.toNNReal r
  let s := Real.toNNReal (1-r)
  have ht : (t:ℝ)=r := Real.coe_toNNReal r hr.1
  have hs : (s:ℝ)=1-r := Real.coe_toNNReal (1-r) (sub_nonneg.mpr hr.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hr.2
  have hs1 : s≤1 := by rw [← NNReal.coe_le_coe,hs,NNReal.coe_one]; linarith [hr.1]
  let v := timeGridCoefficients (a+b) β q
  let f := scalarCDFValue β α r s
  let u := scalarCDFGradient β α r s
  have hsuffix : f=scalarHierarchy b (fun i => m (i.natAdd a))
      (fun i => v (i.natAdd a)) scalarSpinTerminal := by
    funext x
    have H := scalarCDFOperator_eq_partition scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
      β hα hαm b (gridSuffix a b q) (gridSuffix_monotone hq)
      (fun i => m (i.natAdd a)) (fun i => hm (i.natAdd a))
      (fun i z hz => hmodel (i.natAdd a) z hz) s hs1
      (by change (s:ℝ)=q (Fin.last (a+b))-r; rw [hq1,hs]) x
    exact H
  have hu : u=scalarHierarchyAverage b (fun i => m (i.natAdd a))
      (fun i => v (i.natAdd a)) scalarSpinTerminal scalarMagnetization := by
    funext x
    have H := (scalarCDFValue_hasDerivAt β hα hαm r s hs1 x).deriv
    change deriv f x=u x at H
    rw [hsuffix,scalarHierarchy_gradient_average _ _ _ scalarSpinTerminal_regular
      scalarSpinTerminal_hasDerivAt] at H
    exact H.symm
  have HG := scalarCDFGradient_sq_regular β hα hαm r s hs1
  have hp0 : gridPrefix a b q 0=0 := by simpa [gridPrefix] using hq0
  have H := scalarCDFAverage_eq_partition (scalarCDFValue_regular β hα hαm r s hs1)
    HG.1 HG.2.1 (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (B:=1) (C:=2) HG.2.2.1 HG.2.2.2 β hα hαm a (gridPrefix a b q)
    (gridPrefix_monotone hq) (fun i => m (i.castAdd b)) (fun i => hm (i.castAdd b))
    (fun i z hz => hmodel (i.castAdd b) z hz) t ht1
    (by change (t:ℝ)=r-gridPrefix a b q 0; rw [hp0,sub_zero,ht]) 0
  rw [hp0] at H
  change scalarCDFAverage β α 0 t f (fun z => (u z)^2) 0=_ at H
  change scalarCDFAverage β α 0 t f (fun z => (u z)^2) 0=_
  rw [H,scalarMomentSquare_split]
  change scalarHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
    f (fun x => (u x)^2) 0=_
  rw [hsuffix,hu]

end SK.Analytic

end
end

end OAI
