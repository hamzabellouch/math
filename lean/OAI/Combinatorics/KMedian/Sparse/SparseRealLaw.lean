import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteKernels
import OAI.Combinatorics.KMedian.Sparse.SparseIntegerLaw

namespace OAI

namespace MetricKMedian
namespace RationalLaw
variable {α : Type} [Fintype α]

noncomputable def real (μ : RationalLaw α) : FiniteLaw α where
  weight a := (μ.weight a:ℝ)
  nonneg a := by exact_mod_cast μ.nonneg a
  total := by exact_mod_cast μ.total

@[simp] theorem real_expect (μ : RationalLaw α) (f : α → ℚ) :
    μ.real.expect (fun a => (f a:ℝ))=((∑ a, μ.weight a*f a:ℚ):ℝ) := by
  simp only [FiniteLaw.expect,real,Rat.cast_sum,Rat.cast_mul]

end RationalLaw

namespace SparseIntegerLaw
variable {α : Type}

noncomputable def realIndex (μ : SparseIntegerLaw α) : FiniteLaw (Fin μ.length) :=
  μ.law.rational.real

@[simp] theorem realIndex_expect (μ : SparseIntegerLaw α) (f : α → ℚ) :
    μ.realIndex.expect (fun i => (f μ.states[i.val]:ℝ))=(μ.moment f:ℝ) := by
  exact μ.law.rational.real_expect (fun i => f μ.states[i.val])

noncomputable def real [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) : FiniteLaw α :=
  μ.realIndex.map (fun i => μ.states[i.val])

@[simp] theorem real_expect [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) (f : α → ℚ) :
    μ.real.expect (fun a => (f a:ℝ))=(μ.moment f:ℝ) := by
  rw [real,FiniteLaw.expect_map,realIndex_expect]

theorem real_property [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) (P : α → Prop)
    (hP : ∀ i : Fin μ.length, P μ.states[i.val]) : ∀ a, 0 < μ.real.weight a → P a := by
  exact μ.realIndex.property_map (fun i => μ.states[i.val]) P (fun i _ => hP i)

end SparseIntegerLaw
end MetricKMedian

end OAI
