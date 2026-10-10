import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.CycleCalculus

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
noncomputable def mixedTuple {ι : Type*} [LinearOrder ι] {E : ι → Type*}
    (a b : ∀ i, E i) (i : ι) : ∀ j, E j := fun j => if j < i then a j else b j

lemma MultilinearMap.sub_eq_sum_update {ι : Type*} [Fintype ι] [LinearOrder ι]
    {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (M : MultilinearMap ℝ E ℝ) (a b : ∀ i, E i) :
    M a - M b = ∑ i, M (Function.update (mixedTuple a b i) i (a i-b i)) := by
  have h := M.map_sub_map_piecewise a b Finset.univ
  simp only [Finset.piecewise_univ,Finset.mem_univ,true_implies] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  by_cases hji : j=i
  · subst j
    simp
  · by_cases hj : j < i <;> simp [mixedTuple,hj,hji,Ne.symm hji]

lemma IsMetricCurrent.cycle_difference {k : ℕ} {T : Functional X (k+1)}
    (hcur : IsMetricCurrent T) (hT : IntegerRectifiable T) (hz : IsCycle T)
    (a b : Fin (k+2) → BL) :
    hcur.fullMultilinear a - hcur.fullMultilinear b =
      ∑ i, (-1:ℝ)^i.val * T (a i-b i)
        (fun j => ((i.removeNth (mixedTuple a b i)) j : X → ℝ)) := by
  rw [MultilinearMap.sub_eq_sum_update]
  apply Finset.sum_congr rfl
  intro i _
  exact hcur.fullMultilinear_cycle_update hT hz _ _ _

lemma IsMetricCurrent.cycle_difference_bound {k : ℕ} {T : Functional X (k+1)}
    (hcur : IsMetricCurrent T) (hT : IntegerRectifiable T) (hz : IsCycle T)
    (a b : Fin (k+2) → BL) (K : ℝ≥0)
    (ha : ∀ i, LipschitzWith K (a i : X → ℝ))
    (hb : ∀ i, LipschitzWith K (b i : X → ℝ))
    (D : ℝ) (hd : ∀ i x, |(a i : X → ℝ) x - (b i : X → ℝ) x| ≤ D) :
    |hcur.fullMultilinear a - hcur.fullMultilinear b| ≤
      ((k+2:ℕ):ℝ) * (K:ℝ)^(k+1) * mass T * D := by
  rw [hcur.cycle_difference hT hz]
  calc
    |∑ i, (-1:ℝ)^i.val * T (a i-b i)
        (fun j => ((i.removeNth (mixedTuple a b i)) j : X → ℝ))| ≤
      ∑ i : Fin (k+2), (K:ℝ)^(k+1) * mass T * D := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
        have H := hcur.mass_bound_uniform (a i-b i).property (fun _ => K)
          (fun j => show LipschitzWith K
            ((i.removeNth (mixedTuple a b i)) j : X → ℝ) from by
              dsimp [Fin.removeNth,mixedTuple]
              split_ifs <;> first | exact ha _ | exact hb _)
          (hd i)
        simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_assoc,
          Submodule.coe_sub,Pi.sub_apply,mul_comm D] using H
    _ = _ := by simp [mul_assoc]

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter Matrix
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
local notation "BL" => boundedLipSubmodule (X := X)

lemma IsMetricCurrent.cycle_time_lipschitz {k : ℕ} {T : Functional X (k+1)}
    (hcur : IsMetricCurrent T) (hT : IntegerRectifiable T) (hz : IsCycle T)
    (V : ℝ → Fin (k+2) → BL) (K : ℝ≥0)
    (hx : ∀ t i, LipschitzWith K (V t i : X → ℝ))
    (ht : ∀ i x, LipschitzWith K (fun t => (V t i : X → ℝ) x)) :
    LipschitzWith (⟨((k+2:ℕ):ℝ) * (K:ℝ)^(k+1) * mass T * (K:ℝ),by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (mass_nonneg T)) K.coe_nonneg⟩ : ℝ≥0) (fun t => hcur.fullMultilinear (V t)) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro t s
  have H := hcur.cycle_difference_bound hT hz (V t) (V s) K (hx t) (hx s)
    ((K:ℝ)*dist t s) (fun i x => by simpa only [Real.dist_eq] using (ht i x).dist_le_mul t s)
  change |hcur.fullMultilinear (V t) - hcur.fullMultilinear (V s)| ≤
    ((((k+2:ℕ):ℝ) * (K:ℝ)^(k+1) * mass T) * (K:ℝ)) * dist t s
  simpa only [mul_assoc] using H

end CAT0Fillings
end
end

end OAI
