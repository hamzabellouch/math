import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseIntegerLaw

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem moment_add (μ : SparseIntegerLaw α) (f g : α → ℚ) :
    μ.moment (fun a => f a+g a)=μ.moment f+μ.moment g := by
  simp only [moment,mul_add,sum_add_distrib]

theorem moment_mul (μ : SparseIntegerLaw α) (c : ℚ) (f : α → ℚ) :
    μ.moment (fun a => c*f a)=c*μ.moment f := by
  simp only [moment,mul_left_comm,mul_sum]

theorem moment_mul_right (μ : SparseIntegerLaw α) (f : α → ℚ) (c : ℚ) :
    μ.moment (fun a => f a*c)=μ.moment f*c := by
  simp only [moment,← mul_assoc,sum_mul]

end MetricKMedian.SparseIntegerLaw

end OAI
