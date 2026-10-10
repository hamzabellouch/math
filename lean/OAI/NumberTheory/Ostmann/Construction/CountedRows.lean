import OAI.NumberTheory.Ostmann.Construction.GroupedRows

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction

def weightedGroupedRow {α τ : Type*} [Fintype α] [DecidableEq τ]
    (w : α→ℝ) (tag : α→τ) (f : α→ℂ) (t : τ) : ℂ :=
  groupedValue Finset.univ tag (fun x => (w x:ℂ)*f x) t

theorem weightedGroupedRow_pairing {α τ : Type*} [Fintype α] [Fintype τ] [DecidableEq τ]
    (w : α→ℝ) (tag : α→τ) (f : α→ℂ) (G : τ→ℂ) :
    (∑t,G t*weightedGroupedRow w tag f t)=∑x,(w x:ℂ)*(G (tag x)*f x) := by
  simp only [weightedGroupedRow,groupedValue,Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  ring

theorem weightedGroupedRow_square {α τ : Type*} [Fintype α] [Fintype τ] [DecidableEq τ]
    (w : α→ℝ) (tag : α→τ) (f : α→ℂ) :
    ((∑t,‖weightedGroupedRow w tag f t‖^2:ℝ):ℂ)=
      ∑x,∑y,if tag y=tag x then (w x:ℂ)*(w y:ℂ)*f x*conj (f y) else 0 := by
  have hz (t : τ) (ht : t∉Finset.univ.image tag) : weightedGroupedRow w tag f t=0 := by
    unfold weightedGroupedRow groupedValue
    apply Finset.sum_eq_zero
    intro x hx
    obtain ⟨hx,heq⟩ := Finset.mem_filter.mp hx
    exact (ht (Finset.mem_image.mpr ⟨x,hx,heq⟩)).elim
  have hi : (∑t∈Finset.univ.image tag,‖weightedGroupedRow w tag f t‖^2)=
      ∑t,‖weightedGroupedRow w tag f t‖^2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t ht hnot
    rw [hz t hnot,norm_zero,zero_pow (by decide : 2≠0)]
  rw [←hi]
  have hd := diagonal_eq_grouped_squares Finset.univ tag (fun x => (w x:ℂ)*f x)
  change ((∑t∈Finset.univ.image tag,‖groupedValue Finset.univ tag (fun x => (w x:ℂ)*f x) t‖^2:ℝ):ℂ)=_
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

def countedGroupedRow {α β τ : Type*} [Fintype α] [Fintype β] [DecidableEq τ]
    (μ : FinitePrior α) (tag : α→β→τ) (f : α→β→ℂ) (t : τ) : ℂ :=
  weightedGroupedRow (fun x : α×β => μ.mass x.1) (fun x => tag x.1 x.2)
    (fun x => f x.1 x.2) t

theorem countedGroupedRow_pairing {α β τ : Type*} [Fintype α] [Fintype β]
    [Fintype τ] [DecidableEq τ] (μ : FinitePrior α) (tag : α→β→τ)
    (f : α→β→ℂ) (G : τ→ℂ) :
    (∑t,G t*countedGroupedRow μ tag f t)=
      μ.cmean (fun x => ∑v,G (tag x v)*f x v) := by
  unfold countedGroupedRow
  rw [weightedGroupedRow_pairing]
  simp only [Fintype.sum_prod_type,FinitePrior.cmean,Finset.mul_sum]

theorem countedGroupedRow_square {α β τ : Type*} [Fintype α] [Fintype β]
    [Fintype τ] [DecidableEq τ] (μ : FinitePrior α) (tag : α→β→τ)
    (f : α→β→ℂ) :
    ((∑t,‖countedGroupedRow μ tag f t‖^2:ℝ):ℂ)=
      μ.cmean (fun x => μ.cmean (fun y => ∑v,∑w,
        if tag y w=tag x v then f x v*conj (f y w) else 0)) := by
  unfold countedGroupedRow
  rw [weightedGroupedRow_square]
  simp only [Fintype.sum_prod_type,FinitePrior.cmean,Finset.mul_sum,mul_ite,mul_zero]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs <;> ring

end Ostmann.Construction

end

end OAI
