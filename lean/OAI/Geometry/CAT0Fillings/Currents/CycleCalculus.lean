import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.ProductRule
import OAI.Geometry.CAT0Fillings.Currents.AffineCalculus

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter Matrix
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
local notation "BL" => boundedLipSubmodule (X := X)
lemma Foundations.IntegerRectifiable.cycle_update {k : ℕ} {T : Functional X (k+1)}
    (hT : IntegerRectifiable T) (hz : IsCycle T) {b f : X → ℝ}
    (hb : BoundedLip b) (hf : BoundedLip f) (π : Fin (k+1) → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (j : Fin (k+1)) :
    T b (Function.update π j f) =
      (-1:ℝ)^(j.val+1) * T f (Fin.cons b (j.removeNth π)) := by
  have hp := Foundations.IntegerRectifiable.apply_permute hT
    (Foundations.admissible_vecCons hb hf.1 (fun i => hπ (j.succAbove i))) j.cycleRange
  change T b (Fin.cons f (j.removeNth π) ∘ j.cycleRange) = _ at hp
  rw [Fin.cons_comp_cycleRange,Fin.insertNth_removeNth,Fin.sign_cycleRange] at hp
  rw [hp,Foundations.IntegerRectifiable.cycle_product_rule hT hz hb hf _ (fun i => hπ (j.succAbove i))]
  change ((((-1:ℤˣ)^j.val : ℤˣ) : ℤ) : ℝ) *
    (-T f (Fin.cons b (j.removeNth π))) = _
  simp [pow_succ]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma fin_removeNth_succ {α : Type*} {k : ℕ} (v : Fin (k+2) → α) (j : Fin (k+1)) :
    j.succ.removeNth v = Fin.cons (v 0) (j.removeNth (fun i => v i.succ)) := by
  funext i
  refine Fin.cases ?_ (fun l => ?_) i
  · simp [Fin.removeNth_apply]
  · simp [Fin.removeNth_apply]

lemma IsMetricCurrent.fullMultilinear_cycle_update {k : ℕ} {T : Functional X (k+1)}
    (hcur : IsMetricCurrent T) (hT : IntegerRectifiable T) (hz : IsCycle T)
    (v : Fin (k+2) → BL) (i : Fin (k+2)) (g : BL) :
    hcur.fullMultilinear (Function.update v i g) =
      (-1:ℝ)^i.val * T g (fun j => (i.removeNth v j : X → ℝ)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [IsMetricCurrent.fullMultilinear,MultilinearMap.mk'_apply,
      Function.update_self,bl_update_tail_zero,Fin.removeNth_zero]
    simp only [Fin.val_zero,pow_zero,one_mul]
    rfl
  · change T ((Function.update v j.succ g) 0)
      (fun l => ((Function.update v j.succ g) l.succ : X → ℝ)) = _
    rw [Function.update_of_ne (Fin.succ_ne_zero j).symm,bl_update_tail_succ]
    rw [Foundations.IntegerRectifiable.cycle_update hT hz (v 0).property g.property _
      (fun l => (v l.succ).property.1),fin_removeNth_succ]
    congr 2
    funext l
    refine Fin.cases ?_ (fun m => ?_) l <;> rfl

lemma IsMetricCurrent.hasDeriv_cycleAffine {k : ℕ} {T : Functional X (k+1)}
    (hcur : IsMetricCurrent T) (hT : IntegerRectifiable T) (hz : IsCycle T)
    (f g : Fin (k+2) → BL) (t : ℝ) :
    HasDerivAt (fun s => T (f 0 + s • g 0)
      (fun i => (f i.succ + s • g i.succ : BL)))
      (∑ i, (-1:ℝ)^i.val * T (g i)
        (fun j => ((i.removeNth (fun l => f l + t • g l)) j : X → ℝ))) t := by
  have h := hcur.hasDeriv_fullAffine f g t
  convert h using 1
  · rfl
  · symm
    apply Finset.sum_congr rfl
    intro i _
    exact hcur.fullMultilinear_cycle_update hT hz _ i _

end CAT0Fillings

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable
end CAT0Fillings

end
end

end OAI
