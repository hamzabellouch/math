import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.FiniteChartUnionBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_bounded_ball_cover_of_finite_family {n d : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (N : ℕ) (hN : Fintype.card ι ≤ N)
    (r : ℝ) (hr : 0 < r) (a : Ambient d)
    (f : ι → ball (0 : Ambient n) r → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (f i)) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (finiteBallChartUnionConstant d N M) g ∧
      Set.range g ⊆ closedBall a (3 * r) ∧
      ∀ i, closedBall a (3 * r) ∩ Set.range (f i) ⊆ Set.range g := by
  obtain ⟨p, hp, hpRange, hpFix⟩ := exists_nonexpansive_retraction_of_complete_convex
    (closedBall a (3 * r)) ⟨a, mem_closedBall_self (by positivity)⟩
    isClosed_closedBall.isComplete (convex_closedBall a (3 * r))
  let f' (i : ι) := p ∘ f i
  have hLip' : ∀ i, LipschitzWith M (f' i) := by
    intro i
    simpa only [one_mul] using! hp.comp (hLip i)
  have hRange' : ∀ i, Set.range (f' i) ⊆ closedBall a (3 * r) := by
    intro i y hy
    obtain ⟨u, rfl⟩ := hy
    exact hpRange (f i u)
  obtain ⟨h, hh, hcover⟩ := exists_ball_lipschitz_cover_of_bounded_finite_family hn N hN r hr a f' M hLip' hRange'
  refine ⟨p ∘ h, ?_, ?_, ?_⟩
  · simpa only [one_mul] using! hp.comp hh
  · rintro y ⟨u, rfl⟩
    exact hpRange (h u)
  · intro i y hy
    obtain ⟨u, hu⟩ := hy.2
    have hy' : y ∈ Set.range (f' i) := by
      refine ⟨u, ?_⟩
      change p (f i u) = y
      rw [hu, hpFix y hy.1]
    obtain ⟨v, hv⟩ := hcover (mem_iUnion.mpr ⟨i, hy'⟩)
    refine ⟨v, ?_⟩
    change p (h v) = y
    rw [hv, hpFix y hy.1]

end

end RieszRectifiability

end OAI
