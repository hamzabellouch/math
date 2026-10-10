import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseMarginalTools
import OAI.Combinatorics.KMedian.Sparse.SparseMomentAlgebra

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
variable {α : Type}

theorem moment_sub (μ : SparseIntegerLaw α) (f g : α → ℚ) :
    μ.moment (fun a => f a-g a)=μ.moment f-μ.moment g := by
  simp only [moment,mul_sub,Finset.sum_sub_distrib]

theorem moment_affine_pair (μ : SparseIntegerLaw α) (f g : α → ℚ) (a b : ℚ) :
    μ.moment (fun x => (a+f x)*(b+g x))=
      a*b+a*μ.moment g+b*μ.moment f+μ.moment (fun x => f x*g x) := by
  calc
    _ = μ.moment (fun x => a*b+a*g x+b*f x+f x*g x) :=
      μ.moment_congr _ _ (fun _ => by ring)
    _ = _ := by rw [moment_add,moment_add,moment_add,moment_const,moment_mul,moment_mul]

theorem moment_affine_pair_le (μ : SparseIntegerLaw α) (f g : α → ℚ) (a b x y : ℚ)
    (hf : μ.moment f=x) (hg : μ.moment g=y)
    (hpair : μ.moment (fun t => f t*g t) ≤ x*y) :
    μ.moment (fun t => (a+f t)*(b+g t)) ≤ (a+x)*(b+y) := by
  rw [moment_affine_pair,hf,hg]
  nlinarith only [hpair]

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
