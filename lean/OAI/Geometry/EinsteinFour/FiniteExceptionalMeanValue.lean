import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! A continuous scalar curve with finitely many exceptional parameters
still obeys the ordinary mean value bound. -/
namespace PositiveEinsteinFour.Geometry
open Set

theorem image_sub_le_mul_sub_of_deriv_le_off_finite (E : Finset ℝ)
    {f : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ E → DifferentiableAt ℝ f x)
    (hb : ∀ x ∈ Ioo a b, x ∉ E → deriv f x ≤ C) :
    f b - f a ≤ C * (b - a) := by
  classical
  induction E using Finset.induction_on generalizing a b with
  | empty =>
    apply (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hf
      (fun x hx => (hd x (by simpa only [interior_Icc] using hx) (by simp)).differentiableWithinAt)
      (fun x hx => hb x (by simpa only [interior_Icc] using hx) (by simp))
      a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  | @insert t E ht ih =>
    by_cases hti : t ∈ Ioo a b
    · have hleft : f t - f a ≤ C * (t - a) := by
        apply ih hti.1.le (hf.mono (Icc_subset_Icc_right hti.2.le))
        · intro x hx hxE
          exact hd x ⟨hx.1, hx.2.trans hti.2⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt hx.2, hxE⟩)
        · intro x hx hxE
          exact hb x ⟨hx.1, hx.2.trans hti.2⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt hx.2, hxE⟩)
      have hright : f b - f t ≤ C * (b - t) := by
        apply ih hti.2.le (hf.mono (Icc_subset_Icc_left hti.1.le))
        · intro x hx hxE
          exact hd x ⟨hti.1.trans hx.1, hx.2⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt hx.1, hxE⟩)
        · intro x hx hxE
          exact hb x ⟨hti.1.trans hx.1, hx.2⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt hx.1, hxE⟩)
      linarith
    · apply ih hab hf
      · intro x hx hxE
        apply hd x hx
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hti (h ▸ hx), hxE⟩
      · intro x hx hxE
        apply hb x hx
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hti (h ▸ hx), hxE⟩

end PositiveEinsteinFour.Geometry

end OAI
