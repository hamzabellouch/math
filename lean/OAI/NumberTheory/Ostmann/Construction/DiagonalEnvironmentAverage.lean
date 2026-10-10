import OAI.NumberTheory.Ostmann.Construction.ActualEnergySplit
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem FinitePrior.mean_re {α : Type*} [Fintype α] (μ : FinitePrior α) (F : α→ℂ) :
    μ.mean (fun x => (F x).re)=(μ.cmean F).re := by
  simp only [FinitePrior.mean,FinitePrior.cmean,Complex.re_sum,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem finite_diagonal_environment_exchange {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    (μ : FinitePrior α) (ν : FinitePrior β) (S : Finset ℕ) (w : ℕ→ℝ)
    (c : ℝ) (F : ι→α→β→ℕ→ℂ) :
    μ.mean (fun x => ν.mean (fun y => ∑p∈S,c*(∑i,(w p:ℂ)*F i x y p).re))=
      c*(∑i,μ.cmean (fun x => ν.cmean (fun y => ∑p∈S,(w p:ℂ)*F i x y p))).re := by
  simp_rw [←Finset.mul_sum,FinitePrior.mean_mul_left]
  congr 1
  simp_rw [←Complex.re_sum,FinitePrior.mean_re]
  apply congrArg Complex.re
  have he (x : α) (y : β) :
      (∑p∈S,∑i,(w p:ℂ)*F i x y p)=∑i,∑p∈S,(w p:ℂ)*F i x y p := Finset.sum_comm
  simp_rw [Finset.mul_sum,he,FinitePrior.cmean_sum]

end Ostmann.Construction

end

end OAI
