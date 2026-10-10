import Mathlib

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
lemma multilinear_pair_continuous {ι : Type*} [Fintype ι]
    (M : MultilinearMap ℝ (fun _ : ι => ℝ × ℝ) ℝ) : Continuous M := by
  classical
  have he (v : ι → ℝ × ℝ) :
      M v = ∑ s : Finset ι, (∏ i, if i ∈ s then (v i).1 else (v i).2) *
        M (fun i => if i ∈ s then (1,0) else (0,1)) := by
    have hv : v = (fun i => (v i).1 • ((1,0) : ℝ × ℝ)) +
        (fun i => (v i).2 • ((0,1) : ℝ × ℝ)) := by
      funext i
      ext <;> simp
    rw [hv,M.map_add_univ]
    apply Finset.sum_congr rfl
    intro s _
    have hp : s.piecewise (fun i => (v i).1 • ((1,0) : ℝ × ℝ))
        (fun i => (v i).2 • ((0,1) : ℝ × ℝ)) =
        (fun i => (if i ∈ s then (v i).1 else (v i).2) •
          (if i ∈ s then ((1,0) : ℝ × ℝ) else (0,1))) := by
      funext i
      by_cases hi : i ∈ s <;> simp [hi]
    rw [hp,M.map_smul_univ]
    simp only [smul_eq_mul]
    congr 1; simp
  have hf : (fun v => M v) = fun v =>
      ∑ s : Finset ι, (∏ i, if i ∈ s then (v i).1 else (v i).2) *
        M (fun i => if i ∈ s then (1,0) else (0,1)) := funext he
  rw [show M = (fun v => M v) from rfl,hf]
  apply continuous_finsetSum _ fun s _ => ?_
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd _ fun i _ => ?_
  split_ifs <;> fun_prop

noncomputable def multilinearPairContinuous {ι : Type*} [Fintype ι]
    (M : MultilinearMap ℝ (fun _ : ι => ℝ × ℝ) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : ι => ℝ × ℝ) ℝ :=
  ⟨M,multilinear_pair_continuous M⟩

end CAT0Fillings

end
end

end OAI
