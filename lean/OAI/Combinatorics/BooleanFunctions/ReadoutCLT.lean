import OAI.Combinatorics.BooleanFunctions.MomentTransfer
import OAI.Combinatorics.BooleanFunctions.FiniteCLT

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace ReadoutCLT
open MeasureTheory ProbabilityTheory Filter UniformFinite FiniteCLT
open scoped Topology
attribute [local instance] Classical.propDecidable

def test (x : ℝ) : ℝ := (1/2)*SmoothGaussian.tent 1 (1/2) x
def constant : ℝ := (∫ x, test x ∂gaussianReal 0 1)/2

theorem constant_pos : 0 < constant := by
  have h := SmoothGaussian.tent_mass_pos (a := (1:ℝ)) (h := (1/2:ℝ)) (by norm_num)
  unfold constant test
  rw [integral_const_mul]
  positivity

theorem test_le_abs (x : ℝ) : test x ≤ |x| := by
  by_cases h : |x-1| < 1/2
  · have hx := (abs_lt.mp h).1
    have ht := SmoothGaussian.tent_le_one (by norm_num : (0:ℝ) < 1/2) 1 x
    unfold test
    have ha := le_abs_self x
    linarith
  · rw [test,SmoothGaussian.tent_eq_zero (by norm_num : (0:ℝ) < 1/2) (le_of_not_gt h),mul_zero]
    exact abs_nonneg x

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem exists_abs_gain (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) :
    ∃ n : ℕ, 0 < n ∧ constant < average (fun x => |normalizedSum T n x|) := by
  have hc := MomentTransfer.compact_test_tendsto
    (fun n => uniformMeasure (Fin n → α)) (normalizedSum T) (uniform_clt T h0 h1)
    test (by unfold test; fun_prop)
    ((SmoothGaussian.tent_compactSupport (a := (1:ℝ)) (by norm_num : (0:ℝ) < 1/2)).mul_left (f := fun _ : ℝ => (1/2:ℝ)))
  have hl : constant < ∫ x, test x ∂gaussianReal 0 1 := by
    have := constant_pos
    unfold constant at *
    linarith
  obtain ⟨n,hn,hg⟩ := ((eventually_gt_atTop 0).and (hc.eventually (lt_mem_nhds hl))).exists
  refine ⟨n,hn,hg.trans_le ?_⟩
  rw [integral_uniform]
  exact average_mono (fun x => test_le_abs (normalizedSum T n x))

end ReadoutCLT
end SquareRootDegree

end

end OAI
