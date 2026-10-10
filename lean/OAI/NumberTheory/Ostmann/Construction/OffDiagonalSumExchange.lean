import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.FinitePrior

theorem cmean_pair_counted_exchange {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (μ : FinitePrior α) (ν : FinitePrior β) (F : α→β→β→γ→δ→ℂ) :
    μ.cmean (fun u => ν.cmean (fun x => ν.cmean (fun y => ∑v,∑w,F u x y v w)))=
      ν.cmean (fun x => ν.cmean (fun y => ∑v,∑w,μ.cmean (fun u => F u x y v w))) := by
  rw [cmean_comm]
  apply congrArg (cmean ν)
  funext x
  rw [cmean_comm]
  apply congrArg (cmean ν)
  funext y
  simp_rw [cmean_sum]

theorem counted_pair_frequency_exchange {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (μ : FinitePrior α) (R : δ→ℂ) (F : δ→β→γ→α→ℂ) :
    (∑v:β,∑w:γ,μ.cmean (fun u => ∑s:δ,R s*F s v w u))=
      ∑s:δ,R s*(∑v:β,∑w:γ,μ.cmean (F s v w)) := by
  simp_rw [cmean_sum,cmean_mul_left]
  calc
    _ = ∑v:β,∑s:δ,∑w:γ,R s*μ.cmean (F s v w) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact Finset.sum_comm
    _ = ∑s:δ,∑v:β,∑w:γ,R s*μ.cmean (F s v w) := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

end Ostmann.Construction.FinitePrior

end

end OAI
