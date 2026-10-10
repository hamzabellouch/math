import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-! Exact regrouping of the two amplitude indices by support-measure
class, with every original summand retained. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem finite_class_weighted_sum {ι κ : Type*} [DecidableEq κ]
    (I : Finset ι) (classify : ι → κ) (a : ι → ℝ) (w : κ → ℝ) :
    (∑ k∈I.image classify, w k*(∑ i∈I.filter (fun i => classify i=k), a i))=
      ∑ i∈I, w (classify i)*a i := by
  calc
    _ = ∑ k∈I.image classify, ∑ i∈I.filter (fun i => classify i=k), w (classify i)*a i := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem classify hi) _

theorem finite_class_bilinear_sum {ι κ α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset ι) (J : Finset κ) (ci : ι → α) (cj : κ → β)
    (a : ι → ℝ) (b : κ → ℝ) (K : α → β → ℝ) :
    (∑ k∈I.image ci, ∑ l∈J.image cj,
      K k l*(∑ i∈I.filter (fun i => ci i=k), a i)*(∑ j∈J.filter (fun j => cj j=l), b j))=
    ∑ i∈I, ∑ j∈J, K (ci i) (cj j)*a i*b j := by
  calc
    _ = ∑ k∈I.image ci, ∑ j∈J, K k (cj j)*(∑ i∈I.filter (fun i => ci i=k), a i)*b j := by
      apply Finset.sum_congr rfl
      intro k _
      exact finite_class_weighted_sum J cj b (fun l => K k l*(∑ i∈I.filter (fun i => ci i=k), a i))
    _ = ∑ j∈J, ∑ k∈I.image ci, K k (cj j)*(∑ i∈I.filter (fun i => ci i=k), a i)*b j := Finset.sum_comm
    _ = ∑ j∈J, ∑ i∈I, K (ci i) (cj j)*a i*b j := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = (∑ k∈I.image ci, K k (cj j)*(∑ i∈I.filter (fun i => ci i=k), a i))*b j :=
          (Finset.sum_mul ..).symm
        _ = (∑ i∈I, K (ci i) (cj j)*a i)*b j := by
          rw [finite_class_weighted_sum I ci a (fun k => K k (cj j))]
        _ = _ := Finset.sum_mul ..
    _ = _ := Finset.sum_comm

end LipschitzHilbert

end

end OAI
