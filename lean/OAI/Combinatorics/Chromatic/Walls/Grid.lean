import Mathlib
import OAI.Combinatorics.Chromatic.Walls.Pack
import OAI.Combinatorics.Chromatic.Shuffle.RestrictSplit

namespace OAI

section
namespace ElementaryPositivity.PackConvolution
open ElementaryPositivity.ShuffleConvolution
variable {I : Type*} {A : I → Type*}
variable [∀ i,DecidableEq (A i)]
variable {R : Type*} [CommSemiring R]

def grid {s : Pack (A:=A)} (p : Cut s) : Cut s ≃ Cut (left p) × Cut (right p) :=
  (Equiv.piCongrRight fun i => ShuffleConvolution.grid (p i)).trans
    { toFun := fun q => (fun i => (q i).1, fun i => (q i).2)
      invFun := fun q i => (q.1 i,q.2 i)
      left_inv := by intro q; rfl
      right_inv := by intro q; rfl }

lemma grid_inverse_left {s : Pack (A:=A)} (p : Cut s) (q : Cut (left p)) (r : Cut (right p)) :
    left ((grid p).symm (q,r)) = fun i => left q i ∪ left r i := rfl
lemma grid_inverse_right {s : Pack (A:=A)} (p : Cut s) (q : Cut (left p)) (r : Cut (right p)) :
    right ((grid p).symm (q,r)) = fun i => right q i ∪ right r i := rfl

variable [Fintype I]

lemma grid_kernel (w : (Σi,A i) → (Σi,A i) → R)
    {s : Pack (A:=A)} (p : Cut s) (q : Cut (left p)) (r : Cut (right p)) :
    kernel w (left ((grid p).symm (q,r))) (right ((grid p).symm (q,r))) =
      kernel w (left q) (right q) * kernel w (left r) (right r) *
        kernel w (left q) (right r) * kernel w (left r) (right q) := by
  have hl : ∀ i,Disjoint (left q i) (left r i) := fun i =>
    (p i).property.1.mono (q i).left_subset (r i).left_subset
  have hr : ∀ i,Disjoint (right q i) (right r i) := fun i =>
    (p i).property.1.mono (q i).right_subset (r i).right_subset
  rw [grid_inverse_left,grid_inverse_right,
    kernel_union_left w (left q) (left r) (fun i => right q i ∪ right r i) hl,
    kernel_union_right w (left q) (right q) (right r) hr,
    kernel_union_right w (left r) (right q) (right r) hr]
  ac_rfl

variable [DecidableEq I] [∀ i,Fintype (A i)]

theorem shuffle_grid (w : (Σi,A i) → (Σi,A i) → R)
    (f g : Pack (A:=A) → R) {s : Pack (A:=A)} (p : Cut s) :
    shuffle w f g s = ∑ q : Cut (left p), ∑ r : Cut (right p),
      f (fun i => left q i ∪ left r i) * g (fun i => right q i ∪ right r i) *
        (kernel w (left q) (right q) * kernel w (left r) (right r) *
          kernel w (left q) (right r) * kernel w (left r) (right q)) := by
  rw [shuffle,← (grid p).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  rw [grid_kernel,grid_inverse_left,grid_inverse_right]

end ElementaryPositivity.PackConvolution

end

end OAI
