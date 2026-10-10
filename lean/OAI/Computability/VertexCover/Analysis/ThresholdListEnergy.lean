import Mathlib
import OAI.Computability.VertexCover.Reduction.IncrementNorm

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Threshold

noncomputable def slots {ι : Type*} [Fintype ι] (b : ℝ) (g : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun k => b ≤ |g k|)

@[simp] theorem mem_slots {ι : Type*} [Fintype ι] (b : ℝ) (g : ι → ℝ) (k : ι) :
    k ∈ slots b g ↔ b ≤ |g k| := by
  classical
  simp [slots]

theorem coordinate_bound {ι : Type*} [Fintype ι] {g : ι → ℝ}
    (hg : ∑ k, |g k| ≤ 1) (k : ι) : |g k| ≤ 1 := by
  classical
  exact (Finset.single_le_sum (fun i _ => abs_nonneg (g i)) (Finset.mem_univ k)).trans hg

theorem card_mul_le {ι : Type*} [Fintype ι] (b : ℝ) (g : ι → ℝ)
    (hg : ∑ k, |g k| ≤ 1) : (slots b g).card * b ≤ 1 := by
  classical
  calc
    (slots b g).card * b = ∑ _k ∈ slots b g, b := by simp
    _ ≤ ∑ k ∈ slots b g, |g k| := Finset.sum_le_sum (fun k hk => (mem_slots b g k).mp hk)
    _ ≤ ∑ k, |g k| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => abs_nonneg (g k))
    _ ≤ 1 := hg

theorem energy_le {ι : Type*} [Fintype ι] (b : ℝ) (hb : 0 ≤ b) (g : ι → ℝ)
    (hg : ∑ k, |g k| ≤ 1) :
    (∑ k, (g k)^2) ≤ b + ∑ k ∈ slots b g, |g k| := by
  classical
  have hpoint : ∀ k, (g k)^2 ≤ b * |g k| + if k ∈ slots b g then |g k| else 0 := by
    intro k
    have hab := abs_nonneg (g k)
    have hsq : (g k)^2 = |g k|^2 := (sq_abs _).symm
    have hc := coordinate_bound hg k
    by_cases hk : k ∈ slots b g
    · rw [ite_eq_left hk, hsq]
      have := mul_nonneg hb hab
      nlinarith
    · rw [ite_eq_right hk, add_zero, hsq]
      have hk' : |g k| < b := lt_of_not_ge ((mem_slots b g k).not.mp hk)
      nlinarith
  calc
    (∑ k, (g k)^2) ≤ ∑ k, (b * |g k| + if k ∈ slots b g then |g k| else 0) :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = b * (∑ k, |g k|) + ∑ k ∈ slots b g, |g k| := by
      simp [Finset.sum_add_distrib, Finset.mul_sum, slots, Finset.sum_filter]
    _ ≤ b * 1 + ∑ k ∈ slots b g, |g k| := add_le_add (mul_le_mul_of_nonneg_left hg hb) le_rfl
    _ = b + ∑ k ∈ slots b g, |g k| := by ring

end VertexCover.Threshold

namespace VertexCover.LabelCover.Query

noncomputable def thresholdList {Φ : LabelCover} {d : ℕ} (i : Φ.Query d)
    (b : ℝ) (g : Fin (Φ.WeightDimension d) → ℝ) : List i.LocalLabel := by
  classical
  exact i.labels.filter (fun a => decide (b ≤ |g (i.slot a)|))

@[simp] theorem mem_thresholdList {Φ : LabelCover} {d : ℕ} (i : Φ.Query d)
    (b : ℝ) (g : Fin (Φ.WeightDimension d) → ℝ) (a : i.LocalLabel) :
    a ∈ i.thresholdList b g ↔ b ≤ |g (i.slot a)| := by
  classical
  simp [thresholdList]

theorem thresholdList_nodup {Φ : LabelCover} {d : ℕ} (i : Φ.Query d)
    (b : ℝ) (g : Fin (Φ.WeightDimension d) → ℝ) : (i.thresholdList b g).Nodup := by
  classical
  apply List.Nodup.filter
  unfold labels
  exact Finset.sort_nodup _ _

theorem thresholdList_slots {Φ : LabelCover} {d : ℕ} (i : Φ.Query d)
    (b : ℝ) (hb : 0 < b) (g : Fin (Φ.WeightDimension d) → ℝ)
    (hzero : ∀ k, (∀ a : i.LocalLabel, i.slot a ≠ k) → g k = 0) :
    (i.thresholdList b g).toFinset.image i.slot = VertexCover.Threshold.slots b g := by
  classical
  ext k
  simp only [Finset.mem_image, List.mem_toFinset, mem_thresholdList,
    VertexCover.Threshold.mem_slots]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hk
    by_contra hc
    have hz : ∀ a : i.LocalLabel, i.slot a ≠ k := by
      intro a heq
      exact hc ⟨a, heq ▸ hk, heq⟩
    rw [hzero k hz, abs_zero] at hk
    exact (not_le_of_gt hb) hk

theorem thresholdList_card {Φ : LabelCover} {d : ℕ} (i : Φ.Query d)
    (b : ℝ) (g : Fin (Φ.WeightDimension d) → ℝ)
    (hg : ∑ k, |g k| ≤ 1) : (i.thresholdList b g).length * b ≤ (1 : ℝ) := by
  classical
  have hsub : (i.thresholdList b g).toFinset.image i.slot ⊆ VertexCover.Threshold.slots b g := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨a, ha, rfl⟩
    exact (VertexCover.Threshold.mem_slots b g _).mpr ((i.mem_thresholdList b g a).mp
      (List.mem_toFinset.mp ha))
  calc
    (i.thresholdList b g).length * b = ∑ _k ∈ (i.thresholdList b g).toFinset.image i.slot, b := by
      simp [Finset.card_image_of_injective _ i.slot_injective,
        List.toFinset_card_of_nodup (i.thresholdList_nodup b g)]
    _ ≤ ∑ k ∈ (i.thresholdList b g).toFinset.image i.slot, |g k| := by
      apply Finset.sum_le_sum
      intro k hk
      exact (VertexCover.Threshold.mem_slots b g k).mp (hsub hk)
    _ ≤ ∑ k, |g k| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => abs_nonneg (g k))
    _ ≤ 1 := hg

theorem thresholdList_energy {Φ : LabelCover} {d : ℕ} (i : Φ.Query d)
    (b : ℝ) (hb : 0 < b) (g : Fin (Φ.WeightDimension d) → ℝ)
    (hg : ∑ k, |g k| ≤ 1)
    (hzero : ∀ k, (∀ a : i.LocalLabel, i.slot a ≠ k) → g k = 0) :
    (∑ k, (g k)^2) ≤ b + ∑ a ∈ (i.thresholdList b g).toFinset, |g (i.slot a)| := by
  classical
  have heq : (∑ a ∈ (i.thresholdList b g).toFinset, |g (i.slot a)|) =
      ∑ k ∈ VertexCover.Threshold.slots b g, |g k| := by
    rw [← i.thresholdList_slots b hb g hzero,
      Finset.sum_image i.slot_injective.injOn]
  rw [heq]
  exact VertexCover.Threshold.energy_le b hb.le g hg

end VertexCover.LabelCover.Query


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
