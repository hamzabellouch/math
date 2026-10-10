import OAI.Analysis.CircleDomains.Selection.FiniteLineGaps

namespace OAI

/-! Each actual gap of sorted disjoint holes lies in the residual interval. -/
open Set Function
namespace CircleDomainRigidity

 theorem gapsAfterHoles_subset_residual {n : ℕ} {a b : ℝ} (H : Fin n → ℝ × ℝ)
    (hinside : ∀ i, a < (H i).1 ∧ (H i).1 ≤ (H i).2 ∧ (H i).2 < b)
    (hsep : ∀ i j, i < j → (H i).2 < (H j).1) (i : Fin (n + 1)) :
    Ioo (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ⊆
      Icc a b ∩ (⋃ j, Icc (H j).1 (H j).2)ᶜ := by
  have hfirst : Monotone (fun i => (H i).1) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · rfl
    · exact (hinside i).2.1.trans (hsep i j hij).le
  have hlast : Monotone (fun i => (H i).2) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · rfl
    · exact (hsep i j hij).le.trans (hinside j).2.1
  have hleft : a ≤ (gapsAfterHoles a b H i).1 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_rfl
    · exact (hinside j).1.le.trans (hinside j).2.1
  have hright : (gapsAfterHoles a b H i).2 ≤ b := by
    refine Fin.lastCases (motive := fun j : Fin (n + 1) =>
      (gapsAfterHoles a b H j).2 ≤ b) ?_ (fun j => ?_) i
    · simp only [gapsAfterHoles_last_snd, le_refl]
    · simpa only [gapsAfterHoles_castSucc_snd] using (hinside j).2.1.trans (hinside j).2.2.le
  intro x hx
  refine ⟨⟨hleft.trans hx.1.le, hx.2.le.trans hright⟩, ?_⟩
  intro h
  obtain ⟨j, hj⟩ := mem_iUnion.mp h
  exact gapsAfterHoles_avoid a b H hfirst hlast i hx j hj

end CircleDomainRigidity

end OAI
