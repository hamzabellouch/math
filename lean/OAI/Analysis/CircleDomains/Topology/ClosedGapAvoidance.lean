import OAI.Analysis.CircleDomains.Selection.FiniteLineGaps

namespace OAI

/-! Closed retained gaps avoid the interiors of the deleted intervals.
Their endpoints lie on the enlarged circles, outside the original disks. -/
open Set Function
namespace CircleDomainRigidity

 theorem closed_gaps_avoid_hole_interiors {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hfirst : Monotone (fun i => (H i).1)) (hlast : Monotone (fun i => (H i).2))
    (i : Fin (n+1)) {x : ℝ} (hx : x ∈ Icc
      (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2) :
    ∀ j, x ∉ Ioo (H j).1 (H j).2 := by
  intro j hj
  by_cases hji : j.val < i.val
  · obtain ⟨k,rfl⟩ := Fin.eq_succ_of_ne_zero (show i ≠ 0 by
      intro he; simp [he] at hji)
    rw [gapsAfterHoles_succ_fst] at hx
    have hjk : j ≤ k := Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hji)
    exact (not_lt_of_ge ((hlast hjk).trans hx.1)) hj.2
  · obtain ⟨k,rfl⟩ := Fin.eq_castSucc_of_ne_last (show i ≠ Fin.last n by
      intro he; subst i; exact hji j.isLt)
    rw [gapsAfterHoles_castSucc_snd] at hx
    have hkj : k ≤ j := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hji)
    exact (not_lt_of_ge (hx.2.trans (hfirst hkj))) hj.1

 theorem closed_gaps_inside {n : ℕ} {a b : ℝ} (H : Fin n → ℝ × ℝ)
    (hinside : ∀ i, a ≤ (H i).1 ∧ (H i).1 ≤ (H i).2 ∧ (H i).2 ≤ b)
    (i : Fin (n+1)) : Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ⊆ Icc a b := by
  have hl : a ≤ (gapsAfterHoles a b H i).1 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [gapsAfterHoles_zero_fst,le_refl]
    · rw [gapsAfterHoles_succ_fst]
      exact (hinside j).1.trans (hinside j).2.1
  have hr : (gapsAfterHoles a b H i).2 ≤ b := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [gapsAfterHoles_last_snd,le_refl]
    · rw [gapsAfterHoles_castSucc_snd]
      exact (hinside j).2.1.trans (hinside j).2.2
  exact fun _ hx => ⟨hl.trans hx.1,hx.2.trans hr⟩

end CircleDomainRigidity

end OAI
