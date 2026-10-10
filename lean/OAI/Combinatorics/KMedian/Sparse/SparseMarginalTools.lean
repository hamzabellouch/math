import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseIntegerLaw

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

 theorem moment_congr (μ : SparseIntegerLaw α) (f g : α → ℚ)
    (h : ∀ i : Fin μ.length, f μ.states[i.val]=g μ.states[i.val]) :
    μ.moment f=μ.moment g := by
  apply sum_congr rfl
  intro i _
  rw [h i]

 theorem moment_mono (μ : SparseIntegerLaw α) (f g : α → ℚ)
    (h : ∀ i : Fin μ.length, f μ.states[i.val] ≤ g μ.states[i.val]) :
    μ.moment f ≤ μ.moment g := by
  apply sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (h i) (μ.law.rational.nonneg i)

 theorem moment_const (μ : SparseIntegerLaw α) (c : ℚ) : μ.moment (fun _ => c)=c := by
  unfold moment
  rw [← sum_mul,μ.law.rational.total,one_mul]

 def dirac (a : α) : SparseIntegerLaw α where
  length := 1
  states := Vector.replicate 1 a
  law := {
    denominator := 1
    denominator_pos := by norm_num
    numerator := fun _ => 1
    numerator_nonneg := fun _ => by norm_num
    total := by simp }

 theorem dirac_moment (a : α) (f : α → ℚ) : (dirac a).moment f=f a := by
  change (∑ _i : Fin 1, ((1:ℤ):ℚ)/1*f a)=f a
  simp

 theorem dirac_states (a : α) (i : Fin (dirac a).length) : (dirac a).states[i.val]=a := by
  simp [dirac]

end MetricKMedian.SparseIntegerLaw

end OAI
