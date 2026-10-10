import OAI.NumberTheory.Ostmann.Construction.Diagonal
import OAI.NumberTheory.Ostmann.Construction.FiniteTransfer

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction
variable {α τ : Type*} [Fintype α] [Fintype τ] [DecidableEq τ]

def priorGroupedRow (μ : FinitePrior α) (tag : α → τ) (f : α → ℂ) (t : τ) : ℂ :=
  groupedValue Finset.univ tag (fun x => (μ.mass x:ℂ)*f x) t

theorem priorGroupedRow_pairing (μ : FinitePrior α) (tag : α → τ)
    (f : α → ℂ) (G : τ → ℂ) :
    (∑ t,G t*priorGroupedRow μ tag f t)=μ.cmean (fun x => G (tag x)*f x) := by
  simp only [priorGroupedRow,groupedValue,Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  ring

omit [Fintype τ] in
theorem priorGroupedRow_zero_of_not_mem (μ : FinitePrior α) (tag : α → τ) (f : α → ℂ)
    (t : τ) (ht : t∉Finset.univ.image tag) : priorGroupedRow μ tag f t=0 := by
  unfold priorGroupedRow groupedValue
  apply Finset.sum_eq_zero
  intro x hx
  obtain ⟨hx,heq⟩ := Finset.mem_filter.mp hx
  exact (ht (Finset.mem_image.mpr ⟨x,hx,heq⟩)).elim

theorem priorGroupedRow_square (μ : FinitePrior α) (tag : α → τ) (f : α → ℂ) :
    ((∑t,‖priorGroupedRow μ tag f t‖^2 : ℝ):ℂ) =
      ∑x,∑y,if tag y=tag x then
        (μ.mass x:ℂ)*(μ.mass y:ℂ)*f x*conj (f y) else 0 := by
  have hi : (∑t∈Finset.univ.image tag,‖priorGroupedRow μ tag f t‖^2) =
      ∑t,‖priorGroupedRow μ tag f t‖^2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t ht hnot
    rw [priorGroupedRow_zero_of_not_mem μ tag f t hnot,norm_zero,zero_pow (by decide : 2≠0)]
  rw [←hi]
  have hd := diagonal_eq_grouped_squares Finset.univ tag (fun x => (μ.mass x:ℂ)*f x)
  change ((∑t∈Finset.univ.image tag,‖groupedValue Finset.univ tag (fun x => (μ.mass x:ℂ)*f x) t‖^2:ℝ):ℂ)=_
  rw [←hd]
  unfold diagonalComplex
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hxy : tag y=tag x
  · simp only [hxy,ite_true,map_mul,Complex.conj_ofReal]
    ring
  · simp only [hxy,ite_false]

end Ostmann.Construction

end

end OAI
