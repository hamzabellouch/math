import OAI.NumberTheory.CubicMoment.Estimates.FiniteMomentSaving

namespace OAI

/-! One set of analytic parameters suffices for the finitely many
possible ways to group the coordinates of a fixed prime tuple. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_bilinear_constants {σ : Type*} [Fintype σ]
    (e K B : σ → ℝ) (g : σ → ℕ) (he : ∀ s, 0 < e s) :
    ∃ (η : ℝ) (G : ℕ) (C T : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < C ∧
      ∀ s, η ≤ e s ∧ g s ≤ G ∧ K s ≤ C ∧ B s ≤ T := by
  classical
  obtain ⟨d,hd,hde⟩ := finite_positive_lower_bound e he
  refine ⟨min d 1,Finset.univ.sup g,1+∑ s, |K s|,1+∑ s, |B s|,
    lt_min hd zero_lt_one,min_le_right _ _,by positivity,?_⟩
  intro s
  have hK : |K s| ≤ ∑ t, |K t| :=
    Finset.single_le_sum (fun t _ => abs_nonneg (K t)) (Finset.mem_univ s)
  have hB : |B s| ≤ ∑ t, |B t| :=
    Finset.single_le_sum (fun t _ => abs_nonneg (B t)) (Finset.mem_univ s)
  exact ⟨(min_le_left _ _).trans (hde s),Finset.le_sup (f := g) (Finset.mem_univ s),
    by linarith [le_abs_self (K s)],by linarith [le_abs_self (B s)]⟩

end CubicFirstMoment

end

end OAI
