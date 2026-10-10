import Mathlib

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
section
section
section
section
open Finset Filter Topology

namespace CannonFlow

theorem positive_capacity_transitions {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    {L Q : ℝ} (hL : 0 < L) (hQ : 0 < Q) (ht : ∀ i ∈ S, 0 ≤ t i)
    (hc : 1 ≤ ∑ i ∈ S, min (L*t i) (Q*(t i)^2)) :
    ∃ T : Finset ι, T ⊆ S ∧ (∀ i ∈ T, 0 < t i) ∧ ∃ p : T → ℝ,
      (∀ i, 0 < p i) ∧ (∑ i, p i = 1) ∧
      (∀ i, p i ≤ L*t i) ∧ ∀ i, p i ≤ Q*(t i)^2 := by
  classical
  let T := S.filter (fun i => 0 < t i)
  let cap : ι → ℝ := fun i => min (L*t i) (Q*(t i)^2)
  have hsum : (∑ i : T, cap i) = ∑ i ∈ S, cap i := by
    rw [Finset.sum_coe_sort]
    change (∑ i ∈ S.filter (fun i => 0 < t i), cap i) = ∑ i ∈ S, cap i
    apply sum_subset (filter_subset _ _) (fun i hi hit => ?_)
    have hn : ¬ 0 < t i := fun hh => hit (mem_filter.mpr ⟨hi,hh⟩)
    have hz : t i=0 := le_antisymm (le_of_not_gt hn) (ht i hi)
    simp [cap,hz]
  let Z := ∑ i : T, cap i
  have hZ : 1 ≤ Z := by rw [show Z = _ from hsum]; exact hc
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  refine ⟨T,filter_subset _ _,fun i hi => (mem_filter.mp hi).2,
    fun i => cap i/Z,?_,?_,?_,?_⟩
  · intro i
    have hti := (mem_filter.mp i.property).2
    exact div_pos (lt_min (mul_pos hL hti) (mul_pos hQ (sq_pos_of_pos hti))) hZpos
  · rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  · intro i
    have hti := (mem_filter.mp i.property).2
    have hcap : 0 ≤ cap i := le_min (mul_nonneg hL.le hti.le) (mul_nonneg hQ.le (sq_nonneg _))
    have hh : cap i/Z ≤ cap i := (div_le_iff₀ hZpos).mpr (by nlinarith only [hZ,hcap])
    exact hh.trans (min_le_left _ _)
  · intro i
    have hti := (mem_filter.mp i.property).2
    have hcap : 0 ≤ cap i := le_min (mul_nonneg hL.le hti.le) (mul_nonneg hQ.le (sq_nonneg _))
    have hh : cap i/Z ≤ cap i := (div_le_iff₀ hZpos).mpr (by nlinarith only [hZ,hcap])
    exact hh.trans (min_le_right _ _)

theorem uniform_bad_transitions {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    {L Q : ℝ} (hL : 0 < L) (hQ : 0 < Q)
    (ht : ∀ i ∈ S, (1:ℝ)/8 ≤ t i)
    (hcardL : 8 ≤ L*(S.card:ℝ)) (hcardQ : 64 ≤ Q*(S.card:ℝ)) :
    ∃ p : S → ℝ, (∀ i, 0 < p i) ∧ (∑ i, p i = 1) ∧
      (∀ i, p i ≤ L*t i) ∧ ∀ i, p i ≤ Q*(t i)^2 := by
  classical
  have hcard : 0 < (S.card:ℝ) := by
    have hc : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
    by_contra hn
    have hz : (S.card:ℝ)=0 := le_antisymm (le_of_not_gt hn) hc
    rw [hz,mul_zero] at hcardL
    norm_num at hcardL
  refine ⟨fun _ => 1/(S.card:ℝ),fun _ => div_pos zero_lt_one hcard,?_,?_,?_⟩
  · simp only [sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_coe]
    exact mul_div_cancel₀ 1 hcard.ne'
  · intro i
    apply (div_le_iff₀ hcard).mpr
    have hh := mul_le_mul_of_nonneg_right (ht i i.property)
      (mul_nonneg hL.le hcard.le)
    nlinarith only [hh,hcardL]
  · intro i
    apply (div_le_iff₀ hcard).mpr
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/8) (ht i i.property) 2
    have hh' := mul_le_mul_of_nonneg_right hh (mul_nonneg hQ.le hcard.le)
    nlinarith only [hh',hcardQ]

end CannonFlow

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
