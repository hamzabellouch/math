import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.RescaledBallCharts
import OAI.Analysis.RieszRectifiability.Foundations.ImmediateChildPartition

namespace OAI

/-!
# Immediate-child charts on a parent ball

Rescaling immediate-child charts to the parent lattice ball preserves their images and divides
their Lipschitz bounds by the fixed radius ratio of 64. Restricting the rescaled maps to the open
parent ball gives a common parameter domain for all children.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_immediate_child_charts_on_parent_ball {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (f : ∀ i : supportImmediateChildren μ R hR k z, ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (f i)) :
    ∃ F : supportImmediateChildren μ R hR k z → ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
      (∀ i, LipschitzWith (M / 64) (F i)) ∧ ∀ i, Set.range (F i) = Set.range (f i) := by
  classical
  have hcharts (i : supportImmediateChildren μ R hR k z) :
      ∃ g : Ambient n → Ambient d,
        LipschitzOnWith (M / 64) g (ball (0 : Ambient n) (latticeRadius R k)) ∧
        g '' ball (0 : Ambient n) (latticeRadius R k) = Set.range (f i) := by
    have h := exists_rescaled_ball_chart i.val.radius (0 : Ambient n) (1 / 64)
      (by norm_num) (f i) M (hLip i)
    have hdom : i.val.radius / ((1 / 64 : ℝ≥0) : ℝ) = latticeRadius R k := by
      change i.val.radius / (1 / 64 : ℝ) = latticeRadius R k
      rw [supportImmediateChild_radius μ R hR k z i]
      ring
    rw [hdom] at h
    simpa only [one_div, div_eq_mul_inv, one_mul] using! h
  choose g hg hRange using hcharts
  refine ⟨fun i => (ball (0 : Ambient n) (latticeRadius R k)).domRestrict (g i),
    fun i => (hg i).to_restrict, ?_⟩
  intro i
  apply Set.Subset.antisymm
  · rintro y ⟨u, rfl⟩
    exact hRange i ▸ mem_image_of_mem (g i) u.property
  · intro y hy
    obtain ⟨u, hu, he⟩ := hRange i ▸ hy
    exact ⟨⟨u, hu⟩, he⟩

end

end RieszRectifiability

end OAI
