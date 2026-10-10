import OAI.Analysis.Laughlin.ThreeBody.LevelTrace
import OAI.Analysis.Laughlin.ThreeBody.TraceCertificate

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Topology

 theorem trace_mul_list_sum {I : Type*} [Fintype I] (P : Matrix I I ℝ)
    (l : List (Matrix I I ℝ)) :
    Matrix.trace (P*l.sum) = (l.map (fun M => Matrix.trace (P*M))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.sum_cons,List.map_cons,Matrix.mul_add,Matrix.trace_add,ih]

 theorem list_filter_sum_if {I : Type*} (l : List I) (p q : I → Prop)
    [DecidablePred p] [DecidablePred q] (f : I → ℝ) :
    ((l.filter p).map (fun i => if q i then f i else 0)).sum =
      ((l.filter (fun i => p i ∧ q i)).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp,hq,ih]

theorem source_physical_threeBody_trace_identity (Q : ℕ) (hQ : 15 ≤ Q) (z : Fin (Q+1)) :
    Matrix.trace (threeSpinProjector Q (by omega) z * physicalThreeBodyMatrix Q) =
      physicalThreeBodyTraceFormula Q z.val := by
  unfold physicalThreeBodyMatrix
  rw [trace_mul_list_sum]
  simp only [List.map_map,Function.comp_def]
  unfold physicalThreeBodyTraceFormula threeBodyTraceFormula
  apply congrArg List.sum
  apply List.map_congr_left
  intro row hrow
  rw [trace_mul_list_sum]
  simp only [List.map_map,Function.comp_def]
  have he : (((List.range 16).filter (fun T => row.1 ≤ T)).map
      (fun T => Matrix.trace (threeSpinProjector Q (by omega) z * threeBodyLevelMatrix Q row.1 T row.2.1 row.2.2))) =
      (((List.range 16).filter (fun T => row.1 ≤ T)).map
        (fun T => if z.val ≤ T then physicalThreeBodyLevel Q z.val T row.1 row.2.1 row.2.2 else 0)) := by
    apply List.map_congr_left
    intro T hT
    simp only [List.mem_filter,List.mem_range,decide_eq_true_eq] at hT
    exact threeBodyLevelMatrix_trace Q (by omega) z row.1 T row.2.1 row.2.2 (by omega) hT.2
  rw [he,list_filter_sum_if]
  simp only [physicalThreeBodyLevel,max_le_iff,and_comm]

theorem source_physical_threeBody_trace_tendsto (z : ℕ) :
    Filter.Tendsto (fun Q => if h : 15 ≤ Q ∧ z ≤ Q then
      Matrix.trace (threeSpinProjector Q (by omega) ⟨z,by omega⟩ * physicalThreeBodyMatrix Q) else 0)
      Filter.atTop (𝓝 (Certificate.e z : ℝ)) := by
  apply (source_physical_threeBody_trace_formula_tendsto z).congr'
  filter_upwards [Filter.eventually_ge_atTop (max 15 z)] with Q hQ
  rw [dite_eq_left (show 15 ≤ Q ∧ z ≤ Q by omega),source_physical_threeBody_trace_identity Q (by omega)]

end Laughlin.Spin

end OAI
