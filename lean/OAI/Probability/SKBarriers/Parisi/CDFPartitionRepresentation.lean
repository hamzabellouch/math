import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFChainAverage
import OAI.Probability.SKBarriers.Scalar.PartitionChain

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def timeGridCoefficients (n : ℕ) (β : ℝ) (q : Fin (n+1) → ℝ) (i : Fin n) : ℝ :=
  β*Real.sqrt (q i.succ-q i.castSucc)

theorem scalarCDFOperator_eq_partition {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hK : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1)
    (hmodel : ∀ i : Fin n, ∀ z ∈ Ico (q i.castSucc) (q i.succ), α z=m i)
    (t : ℝ≥0) (ht : t ≤ 1) (hd : (t:ℝ)=q (Fin.last n)-q 0) (x : ℝ) :
    scalarCDFOperator β α (q 0) t f x=scalarHierarchy n m (timeGridCoefficients n β q) f x := by
  have hdur : chainDuration (partitionTimeChain n q hq m)=t := by
    apply NNReal.coe_injective
    exact (partitionTimeChain_duration n q hq m).trans hd.symm
  have hml (p) (hp : p ∈ partitionTimeChain n q hq m) : p.1 ∈ Icc (0:ℝ) 1 := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact hm i
  have H := scalarCDFOperator_eq_chain hf hK β hα hαm (partitionTimeChain n q hq m) hml
    (q 0) t ht hdur (partitionTimeChain_models n q hq m hmodel) x
  simp only [partitionTimeChain,scalarTimeChain_ofFn,NNReal.coe_mk] at H
  exact H

theorem scalarHierarchyAverage_cast {n l : ℕ} (hn : n=l) (m v : Fin l → ℝ)
    (f g : ℝ → ℝ) :
    scalarHierarchyAverage n (fun i => m (Fin.cast hn i)) (fun i => v (Fin.cast hn i)) f g=
      scalarHierarchyAverage l m v f g := by
  subst l
  rfl

theorem scalarTimeChainAverage_ofFn (n : ℕ) (β : ℝ) (p : Fin n → ℝ × ℝ≥0) (f g : ℝ → ℝ) :
    scalarTimeChainAverage β (List.ofFn p) f g=
      scalarHierarchyAverage n (fun i => (p i).1) (fun i => β*Real.sqrt ((p i).2:ℝ)) f g := by
  unfold scalarTimeChainAverage
  simp only [List.get_ofFn]
  exact scalarHierarchyAverage_cast (show (List.ofFn p).length=n from List.length_ofFn)
    (fun i => (p i).1) (fun i => β*Real.sqrt ((p i).2:ℝ)) f g

theorem scalarCDFAverage_eq_partition {f g dg : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : ∀ y, HasDerivAt g (dg y) y) (hdg : Continuous dg)
    {K B C : ℝ≥0} (hK : LipschitzWith K f) (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (β : ℝ) {α : ℝ → ℝ} (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1)
    (hmodel : ∀ i : Fin n, ∀ z ∈ Ico (q i.castSucc) (q i.succ), α z=m i)
    (t : ℝ≥0) (ht : t ≤ 1) (hd : (t:ℝ)=q (Fin.last n)-q 0) (x : ℝ) :
    scalarCDFAverage β α (q 0) t f g x=scalarHierarchyAverage n m (timeGridCoefficients n β q) f g x := by
  have hdur : chainDuration (partitionTimeChain n q hq m)=t := by
    apply NNReal.coe_injective
    exact (partitionTimeChain_duration n q hq m).trans hd.symm
  have hml (p) (hp : p ∈ partitionTimeChain n q hq m) : p.1 ∈ Icc (0:ℝ) 1 := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact hm i
  have H := scalarCDFAverage_eq_chainAverage hf hg hdg hK hB hC β hα hαm
    (partitionTimeChain n q hq m) hml (q 0) t ht hdur (partitionTimeChain_models n q hq m hmodel) x
  simp only [partitionTimeChain,scalarTimeChainAverage_ofFn,NNReal.coe_mk] at H
  exact H

end SK.Analytic

end
end

end OAI
