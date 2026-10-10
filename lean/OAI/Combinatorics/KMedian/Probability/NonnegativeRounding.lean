import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalRounding

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset

theorem uniform_nonnegative_rounding {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℕ, ∀ (I J X : Type) [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] [Nonempty J] [PseudoMetricSpace X],
      ∀ (y : I → ℚ) (x : J → I → ℚ) (d : J → I → ℚ)
        (client : J → X) (location : I → X),
        (∀ i, 0 ≤ y i) → (∀ i, y i ≤ 1) →
        (∀ j i, 0 ≤ x j i ∧ x j i ≤ y i) → (∀ j, ∑ i, x j i=1) →
        (∀ j i, (d j i:ℝ)=dist (client j) (location i)) →
        ∃ O : Finset I, ∃ a : J → I,
          (∀ j, a j ∈ O) ∧ O.Nonempty ∧ (O.card:ℝ) ≤ (∑ i, (y i:ℝ))+(C:ℝ) ∧
          (∑ j, dist (client j) (location (a j))) ≤
            (1+2/Real.exp 1+ε)*(∑ j, ∑ i, (x j i:ℝ)*dist (client j) (location i)) := by
  obtain ⟨C,hC⟩ := uniform_rational_rounding hε
  refine ⟨C,?_⟩
  intro I J X _ _ _ _ _ _ y x d client location hy hy1 hx hxsum hd
  let P := {i : I // 0 < y i}
  have hyzero : ∀ i, ¬ 0 < y i → y i=0 := fun i hi => le_antisymm (le_of_not_gt hi) (hy i)
  have hxzero : ∀ j i, ¬ 0 < y i → x j i=0 := by
    intro j i hi
    exact le_antisymm ((hx j i).2.trans_eq (hyzero i hi)) (hx j i).1
  have hsumx : ∀ j, (∑ i : P, x j i.val)=1 := by
    intro j
    have he := sum_congr_set {i | 0 < y i} (x j) (fun i => x j i.val)
      (fun _ _ => rfl) (hxzero j)
    exact he.symm.trans (hxsum j)
  have hsumy : (∑ i : P, (y i.val:ℝ))=∑ i, (y i:ℝ) := by
    symm
    apply sum_congr_set {i | 0 < y i} (fun i => (y i:ℝ)) (fun i => (y i.val:ℝ))
      (fun _ _ => rfl)
    intro i hi
    rw [hyzero i hi,Rat.cast_zero]
  have hsumcost : ∀ j, (∑ i : P, (x j i.val:ℝ)*dist (client j) (location i.val))=
      ∑ i, (x j i:ℝ)*dist (client j) (location i) := by
    intro j
    symm
    apply sum_congr_set {i | 0 < y i} (fun i => (x j i:ℝ)*dist (client j) (location i))
      (fun i => (x j i.val:ℝ)*dist (client j) (location i.val)) (fun _ _ => rfl)
    intro i hi
    rw [hxzero j i hi,Rat.cast_zero,zero_mul]
  obtain ⟨O,a,ha,hO,hcount,hconn⟩ := hC P J X (fun i => y i.val) (fun j i => x j i.val)
    (fun j i => d j i.val) client (fun i => location i.val) (fun i => i.property)
    (fun i => hy1 i) (fun j i => hx j i) hsumx (fun j i => hd j i)
  refine ⟨O.image Subtype.val,fun j => (a j).val,fun j => mem_image.mpr ⟨a j,ha j,rfl⟩,
    hO.image _,?_,?_⟩
  · rw [hsumy] at hcount
    exact (show ((O.image Subtype.val).card:ℝ) ≤ (O.card:ℝ) by exact_mod_cast card_image_le).trans hcount
  · simpa only [hsumcost] using hconn

end MetricKMedian.Preparation
end
end

end OAI
