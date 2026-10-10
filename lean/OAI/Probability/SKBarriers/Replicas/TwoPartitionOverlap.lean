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

theorem scalarCDFOverlap_eq_two_partitions (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hq : Monotone q) (hp : Monotone p) (hq0 : q 0=0) (hp1 : p (Fin.last b)=1)
    (hr : q (Fin.last a)=p 0) (m : Fin a → ℝ) (l : Fin b → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hl : ∀ i, l i∈Icc (0:ℝ) 1)
    (hmodelq : ∀ i : Fin a, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i)
    (hmodelp : ∀ i : Fin b, ∀ z∈Ico (p i.castSucc) (p i.succ), α z=l i) :
    scalarCDFOverlap β α (p 0)=
      scalarMomentSquare (a+b) (Fin.append m l)
        (Fin.append (timeGridCoefficients a β q) (timeGridCoefficients b β p))
        scalarSpinTerminal scalarMagnetization ⟨a,by omega⟩ 0 := by
  let r := p 0
  have hr0 : r∈Icc (0:ℝ) 1 := by
    constructor
    · change 0 ≤ p 0
      rw [← hr,← hq0]; exact hq (Fin.zero_le _)
    · rw [← hp1]; exact hp (Fin.le_last _)
  let t := Real.toNNReal r
  let s := Real.toNNReal (1-r)
  have ht : (t:ℝ)=r := Real.coe_toNNReal r hr0.1
  have hs : (s:ℝ)=1-r := Real.coe_toNNReal (1-r) (sub_nonneg.mpr hr0.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hr0.2
  have hs1 : s≤1 := by rw [← NNReal.coe_le_coe,hs,NNReal.coe_one]; linarith [hr0.1]
  let f := scalarCDFValue β α r s
  let u := scalarCDFGradient β α r s
  have hsuffix : f=scalarHierarchy b l (timeGridCoefficients b β p) scalarSpinTerminal := by
    funext x
    exact scalarCDFOperator_eq_partition scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
      β hα hαm b p hp l hl hmodelp s hs1 (by rw [hp1]; exact hs) x
  have hu : u=scalarHierarchyAverage b l (timeGridCoefficients b β p)
      scalarSpinTerminal scalarMagnetization := by
    funext x
    have H := (scalarCDFValue_hasDerivAt β hα hαm r s hs1 x).deriv
    change deriv f x=u x at H
    rw [hsuffix,scalarHierarchy_gradient_average _ _ _ scalarSpinTerminal_regular
      scalarSpinTerminal_hasDerivAt] at H
    exact H.symm
  have HG := scalarCDFGradient_sq_regular β hα hαm r s hs1
  have H := scalarCDFAverage_eq_partition (scalarCDFValue_regular β hα hαm r s hs1)
    HG.1 HG.2.1 (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (B:=1) (C:=2) HG.2.2.1 HG.2.2.2 β hα hαm a q hq m hm hmodelq t ht1
    (by rw [hr,hq0,sub_zero]; exact ht) 0
  rw [hq0] at H
  change scalarCDFAverage β α 0 t f (fun z => (u z)^2) 0=_ at H
  change scalarCDFAverage β α 0 t f (fun z => (u z)^2) 0=_
  rw [H,scalarMomentSquare_split]
  simp only [Fin.append_left,Fin.append_right]
  rw [← hsuffix,← hu]

end SK.Analytic

end
end

end OAI
