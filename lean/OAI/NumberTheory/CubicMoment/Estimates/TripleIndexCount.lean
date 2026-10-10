import OAI.NumberTheory.CubicMoment.Estimates.SmoothPartitionCount
import Mathlib.Order.Interval.Finset.Nat

namespace OAI

/-! Counting the three smooth norm indices near the balanced
configuration. The bound is independent of their common large offset. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma tripleIndex_interval (f : Fin 3 → ℕ) {N C D : ℕ}
    (hlo : N ≤ ∑ i, f i) (hhi : (∑ i, f i) ≤ N+C)
    (hspread : ∀ i j, f i ≤ f j+D) (i : Fin 3) :
    N/3-D ≤ f i ∧ f i ≤ N/3+C+D+1 := by
  have he : (∑ j : Fin 3, f j) = f 0+f 1+f 2 := by simp [Fin.sum_univ_succ,add_assoc]
  rw [he] at hlo hhi
  have h0 := hspread 0 i
  have h1 := hspread 1 i
  have h2 := hspread 2 i
  have hi0 := hspread i 0
  have hi1 := hspread i 1
  have hi2 := hspread i 2
  omega

def tripleIndexCluster (M N C D : ℕ) : Finset (Fin 3 → Fin M) :=
  Finset.univ.filter (fun f => N ≤ ∑ i, (f i).val ∧
    (∑ i, (f i).val) ≤ N+C ∧ ∀ i j, (f i).val ≤ (f j).val+D)

theorem tripleIndexCluster_card (M N C D : ℕ) :
    (tripleIndexCluster M N C D).card ≤ (C+2*D+2)^3 := by
  let S := tripleIndexCluster M N C D
  let F : (Fin 3 → Fin M) → (Fin 3 → ℕ) := fun f i => (f i).val
  have hF : Function.Injective F := by
    intro f g h
    funext i
    exact Fin.ext (congrFun h i)
  have hsub : S.image F ⊆ Fintype.piFinset
      (fun _ : Fin 3 => Finset.Icc (N/3-D) (N/3+C+D+1)) := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨_,hlo,hhi,hspread⟩ := Finset.mem_filter.mp hg
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_Icc.mpr (tripleIndex_interval (fun i => (g i).val) hlo hhi hspread i)
  calc
    S.card = (S.image F).card := (Finset.card_image_of_injective S hF).symm
    _ ≤ (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (N/3-D) (N/3+C+D+1))).card :=
      Finset.card_le_card hsub
    _ = (N/3+C+D+1+1-(N/3-D))^3 := by simp [Fintype.card_piFinset]
    _ ≤ (C+2*D+2)^3 := Nat.pow_le_pow_left (by omega) 3

end CubicFirstMoment

end

end OAI
