import OAI.Analysis.LipschitzHilbert.Phase.SourceSelectionAngularGeometry
import Mathlib.Data.Finset.Card

namespace OAI

/-! Separated-scale disjointness limits all boxes through a point to one
fixed window of scales. This converts per-scale lattice counts into the
uniform packing estimate used in the Bessel argument. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem scale_window_packing {ι X : Type*} (S : Finset ι)
    (level : ι → ℕ) (box : ι → Set X) (gap : ℕ) (B : ℝ)
    (hdisjoint : ∀ i∈S, ∀ j∈S, level i+gap≤level j → Disjoint (box i) (box j))
    (hscale : ∀ z k, ((S.filter fun i => level i=k ∧ z∈box i).card:ℝ)≤B)
    (z : X) : ((S.filter fun i => z∈box i).card:ℝ)≤gap*B := by
  classical
  let active := S.filter fun i => z∈box i
  by_cases hne : active.Nonempty
  · obtain ⟨i,hi,hmin⟩ := active.exists_min_image level hne
    let bins := Finset.Ico (level i) (level i+gap)
    have hmaps : (active:Set ι).MapsTo level bins := by
      intro j hj
      refine Finset.mem_Ico.mpr ⟨hmin j hj,?_⟩
      by_contra hn
      have hle : level i+gap≤level j := le_of_not_gt hn
      have hid := Finset.mem_filter.mp hi
      have hjd := Finset.mem_filter.mp hj
      exact Set.disjoint_left.mp (hdisjoint i hid.1 j hjd.1 hle) hid.2 hjd.2
    have hfiber (k : ℕ) : ((active.filter fun j => level j=k).card:ℝ)≤B := by
      apply (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans (hscale z k)
      intro j hj
      obtain ⟨hj,hk⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjS,hjz⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hjS,hk,hjz⟩
    have hcount : bins.card=gap := by simp [bins]
    change (active.card:ℝ)≤_
    rw [Finset.card_eq_sum_card_fiberwise hmaps,Nat.cast_sum]
    calc
      _ ≤ ∑ k∈bins, B := Finset.sum_le_sum (fun k _ => hfiber k)
      _ = _ := by simp only [Finset.sum_const,hcount,nsmul_eq_mul]
  · have hzero : active=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hB : 0≤B := by
      have h := hscale z 0
      exact (Nat.cast_nonneg _).trans h
    change (active.card:ℝ)≤_
    rw [hzero,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hB

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem length_scale_gap (i j : Fin N) (gap : ℕ) (hgap : i.val+gap≤j.val) :
    (2:ℝ)^gap*P.length j≤P.length i := by
  have he : (2:ℝ)^(i.val+gap)≤(2:ℝ)^j.val :=
    pow_le_pow_right₀ (by norm_num) hgap
  rw [pow_add] at he
  unfold length
  apply (le_div_iff₀ (pow_pos (by norm_num) _)).mpr
  calc
    _ = (P.topLength*((2:ℝ)^i.val*2^gap))/2^j.val := by ring
    _ ≤ P.topLength := (div_le_iff₀ (pow_pos (by norm_num) _)).mpr
      (mul_le_mul_of_nonneg_left he P.topLength_pos.le)

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
