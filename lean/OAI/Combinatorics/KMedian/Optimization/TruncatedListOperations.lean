import Mathlib
import OAI.Combinatorics.KMedian.Optimization.ProjectedSubgradient
import OAI.Combinatorics.KMedian.Optimization.TruncatedObjective
import OAI.Combinatorics.KMedian.Optimization.SimplexListProgram
import OAI.Combinatorics.KMedian.Optimization.DualListOperations

namespace OAI


                                               
section
namespace MetricKMedian.LPBinary
open Finset
theorem range_ofFn (n : ℕ) : List.range n=List.ofFn (fun i : Fin n => i.val) := by
  apply List.ext_getElem
  · simp
  · intros; simp

namespace Truncated

def row (ds : Row) (H : ℚ) : Row := ds.map (fun d => if d≤1 then d else H)
def matrix (ds : Rows) (H : ℚ) : Rows := ds.map (fun d => row d H)
def objective (ds : Rows) (ys : Row) (H : ℚ) : ℚ := ((matrix ds H).map (fun d => Dual.value d ys H)).sum

def component (ds : Rows) (ys : Row) (H : ℚ) (i : ℕ) : ℚ :=
  ((matrix ds H).map (fun d => -max 0 (Dual.best d ys H-d[i]?.getD 0))).sum

def gradient (ds : Rows) (ys : Row) (H : ℚ) : Row :=
  (List.range ys.length).map (component ds ys H)

def next (ds : Rows) (ys : Row) (H k rate : ℚ) : Row :=
  project ((ys.zip (gradient ds ys H)).map (fun p => p.1-rate*p.2)) k

 theorem row_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (H : ℚ) (j : Fin m) :
    row (List.ofFn (d j)) H=List.ofFn (TruncatedLP.truncated d H j) := by
  simp only [row,List.map_ofFn]
  rfl
 theorem matrix_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (H : ℚ) :
    matrix (List.ofFn (fun j => List.ofFn (d j))) H=List.ofFn (fun j => List.ofFn (TruncatedLP.truncated d H j)) := by
  simp only [matrix,List.map_ofFn]
  congr 1
  funext j
  exact row_ofFn d H j
 theorem objective_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (y : Fin n → ℚ) (H : ℚ) :
    objective (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn y) H=TruncatedLP.objective d y H := by
  simp only [objective,matrix_ofFn,List.map_ofFn,List.sum_ofFn,TruncatedLP.objective]
  apply sum_congr rfl
  intro j _
  exact Dual.value_ofFn _ _ _
 theorem component_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (y : Fin n → ℚ) (H : ℚ) (i : Fin n) :
    component (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn y) H i.val=TruncatedLP.gradient d y H i := by
  simp only [component,matrix_ofFn,List.map_ofFn,List.sum_ofFn,TruncatedLP.gradient]
  apply sum_congr rfl
  intro j _
  simp only [Function.comp_apply,Dual.best_ofFn,Gaussian.ListOperation.get_ofFn,FractionalDual.gradient]
 theorem gradient_ofFn {n m : ℕ} (d : Fin m → Fin n → ℚ) (y : Fin n → ℚ) (H : ℚ) :
    gradient (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn y) H=List.ofFn (TruncatedLP.gradient d y H) := by
  simp only [gradient,List.length_ofFn]
  rw [range_ofFn,List.map_ofFn]
  congr 1
  funext i
  exact component_ofFn d y H i
 theorem next_ofFn {n m : ℕ} [NeZero n] (d : Fin m → Fin n → ℚ) (y : Fin n → ℚ) (H k rate : ℚ) :
    next (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn y) H k rate=
      List.ofFn (ProjectedSubgradient.point (ProjectedSubgradient.next k rate (fun y => TruncatedLP.gradient d y H) (Vector.ofFn y))) := by
  simp only [next,gradient_ofFn,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,project_ofFn]
  congr 1
  funext i
  simp only [ProjectedSubgradient.next_apply,ProjectedSubgradient.point_ofFn]
  simp only [ProjectedSubgradient.point_ofFn_apply,Function.comp_def]
end Truncated
end MetricKMedian.LPBinary
end

end OAI
