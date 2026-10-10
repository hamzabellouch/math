import Mathlib

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
namespace VertexCover.Restriction
open scoped BigOperators

noncomputable def batches (d h : ℕ) : Finset (Finset (Fin d)) := by
  classical
  exact Finset.univ.powersetCard h

@[simp] theorem mem_batches {d h : ℕ} {J : Finset (Fin d)} :
    J ∈ batches d h ↔ J.card = h := by
  classical
  simp [batches]

@[simp] theorem card_batches (d h : ℕ) : (batches d h).card = d.choose h := by
  classical
  simp [batches]

theorem sum_if_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (g : ι → ℝ) : (∑ i : ι, if i ∈ J then g i else 0) = ∑ i ∈ J, g i := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

theorem batches_subset_count {d h : ℕ} (S : Finset (Fin d)) (hs : S.card ≤ h) (z : ℝ) :
    (∑ J ∈ batches d h, if S ⊆ J then z else 0) = (d-S.card).choose (h-S.card) * z := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hc : ((batches d h).filter (S ⊆ ·)).card = (d-S.card).choose (h-S.card) := by
    simpa only [batches, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_powersetCard_subset S Finset.univ h (Finset.subset_univ _) hs
  exact_mod_cast hc

theorem batches_singleton_sum {d h : ℕ} (hh : 1 ≤ h) (g : Fin d → ℝ) :
    (∑ J ∈ batches d h, ∑ j ∈ J, g j) = ((d-1).choose (h-1) : ℝ) * ∑ j, g j := by
  classical
  have he : (∑ J ∈ batches d h, ∑ j ∈ J, g j) =
      ∑ J ∈ batches d h, ∑ j : Fin d, if j ∈ J then g j else 0 := by
    apply Finset.sum_congr rfl
    intro J _
    exact (sum_if_mem J g).symm
  rw [he, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Finset.singleton_subset_iff, Finset.card_singleton] using
    batches_subset_count ({j} : Finset (Fin d)) (by simpa using hh) (g j)

theorem batches_pair_sum_le {d h : ℕ} (hh : 2 ≤ h) (g : Fin d → Fin d → ℝ)
    (hg : ∀ j k, 0 ≤ g j k) :
    (∑ J ∈ batches d h, ∑ j ∈ J, ∑ k ∈ J.erase j, g j k) ≤
      ((d-2).choose (h-2) : ℝ) * ∑ j, ∑ k, g j k := by
  classical
  have he : (∑ J ∈ batches d h, ∑ j ∈ J, ∑ k ∈ J.erase j, g j k) =
      ∑ J ∈ batches d h, ∑ j : Fin d, ∑ k : Fin d,
        if j ∈ J ∧ k ∈ J.erase j then g j k else 0 := by
    apply Finset.sum_congr rfl
    intro J _
    rw [← sum_if_mem J (fun j => ∑ k ∈ J.erase j, g j k)]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · simpa only [hj, ite_true, true_and] using (sum_if_mem (J.erase j) (g j)).symm
    · simp only [hj, ite_false, false_and, Finset.sum_const_zero]
  rw [he, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k = j
  · subst k
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, and_false, ite_false, Finset.sum_const_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (hg j j)
  · have hc : ({j,k} : Finset (Fin d)).card = 2 := by simp [Ne.symm hk]
    have hc' := batches_subset_count ({j,k} : Finset (Fin d)) (by omega : _ ≤ h) (g j k)
    simpa only [hc, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      Finset.mem_erase, hk, ne_eq, not_false_eq_true, true_and] using hc'.le

theorem batches_triple_sum_le {d h : ℕ} {E : Type*} [Fintype E]
    (hh : 3 ≤ h) (a b : E → Fin d) (hab : ∀ e, a e ≠ b e)
    (g : Fin d → E → ℝ) (hg : ∀ j e, 0 ≤ g j e) :
    (∑ J ∈ batches d h, ∑ j ∈ J,
      ∑ e ∈ Finset.univ.filter (fun e => a e ∈ J ∧ b e ∈ J ∧ ¬ (a e = j ∨ b e = j)),
        g j e) ≤ ((d-3).choose (h-3) : ℝ) * ∑ j, ∑ e, g j e := by
  classical
  have he : (∑ J ∈ batches d h, ∑ j ∈ J,
      ∑ e ∈ Finset.univ.filter (fun e => a e ∈ J ∧ b e ∈ J ∧ ¬ (a e = j ∨ b e = j)),
        g j e) = ∑ J ∈ batches d h, ∑ j : Fin d, ∑ e : E,
      if j ∈ J ∧ a e ∈ J ∧ b e ∈ J ∧ ¬ (a e = j ∨ b e = j) then g j e else 0 := by
    apply Finset.sum_congr rfl
    intro J _
    rw [← sum_if_mem J (fun j => ∑ e ∈ Finset.univ.filter
      (fun e => a e ∈ J ∧ b e ∈ J ∧ ¬ (a e = j ∨ b e = j)), g j e)]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · simp only [hj, ite_true, true_and, Finset.sum_filter]
    · simp only [hj, ite_false, false_and, Finset.sum_const_zero]
  rw [he, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases hje : a e = j ∨ b e = j
  · simp only [hje, not_true_eq_false, and_false, ite_false, Finset.sum_const_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (hg j e)
  · obtain ⟨ha, hb⟩ := not_or.mp hje
    have hc : ({j, a e, b e} : Finset (Fin d)).card = 3 := by
      simp [Ne.symm ha, Ne.symm hb, hab e]
    have hc' := batches_subset_count ({j,a e,b e} : Finset (Fin d))
      (by omega : _ ≤ h) (g j e)
    simpa only [hc, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      hje, not_false_eq_true, and_true] using hc'.le

end VertexCover.Restriction


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
