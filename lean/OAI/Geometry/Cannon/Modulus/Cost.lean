import Mathlib
import OAI.Geometry.Cannon.Modulus.Weights

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace

namespace CannonCells

open Set

variable {X ι : Type*} [Fintype ι]

noncomputable def cost (C : ι → Set X) (w : ι → ℝ) (A : Set X) : ℝ :=
  ∑ i ∈ indices C A, w i

lemma cost_nonneg (C : ι → Set X) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (A : Set X) :
    0 ≤ cost C w A := Finset.sum_nonneg (fun i _ => hw i)

lemma indices_mono (C : ι → Set X) {A B : Set X} (h : A ⊆ B) : indices C A ⊆ indices C B := by
  intro i hi
  obtain ⟨x,hx,hxi⟩ := (mem_indices C A i).mp hi
  exact (mem_indices C B i).mpr ⟨x,h hx,hxi⟩

lemma cost_mono (C : ι → Set X) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {A B : Set X} (h : A ⊆ B) : cost C w A ≤ cost C w B := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (indices_mono C h) (fun i _ _ => hw i)

lemma indices_union [DecidableEq ι] (C : ι → Set X) (A B : Set X) :
    indices C (A ∪ B) = indices C A ∪ indices C B := by
  classical
  ext i
  simp only [mem_indices,Finset.mem_union,union_inter_distrib_right,union_nonempty]

lemma cost_union_le (C : ι → Set X) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (A B : Set X) :
    cost C w (A ∪ B) ≤ cost C w A + cost C w B := by
  classical
  unfold cost
  rw [indices_union]
  have h := Finset.sum_union_inter (s₁ := indices C A) (s₂ := indices C B) (f := w)
  have hn : 0 ≤ ∑ i ∈ indices C A ∩ indices C B, w i :=
    Finset.sum_nonneg (fun i _ => hw i)
  linarith

end CannonCells

end
end
end
end
end
end
end
end
end

end OAI
