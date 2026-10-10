import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.FiniteChartUnionBounds
import OAI.Analysis.RieszRectifiability.Surfaces.ImmediateChildChartRescaling

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def immediateChildAssemblyConstant (d : ℕ) (M : ℝ≥0) : ℝ≥0 :=
  finiteBallChartUnionConstant d (257 ^ d) (M / 64)

theorem exists_immediate_child_chart_assembly {n d : ℕ} (hn : 0 < n)
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (f : ∀ i : supportImmediateChildren μ R hR k z, ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (f i))
    (himage : ∀ i, Set.range (f i) ⊆ closedBall i.val.center (2 * i.val.radius)) :
    ∃ g : ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
      LipschitzWith (immediateChildAssemblyConstant d M) g ∧
      Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
      (∀ i, i.val.cell ∩ Set.range (f i) ⊆ Set.range g) ∧
      μ (cleanSupportCell μ R hR k z \ Set.range g) ≤
        ∑ i : supportImmediateChildren μ R hR k z, μ (i.val.cell \ Set.range (f i)) := by
  classical
  have hr : 0 < latticeRadius R k := latticeRadius_pos R hR k
  obtain ⟨F, hF, hFRange⟩ := exists_immediate_child_charts_on_parent_ball μ R hR k z f M hLip
  have hcount : Fintype.card (supportImmediateChildren μ R hR k z) ≤ 257 ^ d := by
    simpa using! supportImmediateChildren_card_le μ R hR k z
  have hFImage (i : supportImmediateChildren μ R hR k z) :
      Set.range (F i) ⊆ closedBall (z : Ambient d) (3 * latticeRadius R k) := by
    intro y hy
    have hnear : dist y i.val.center ≤ 2 * i.val.radius := himage i (hFRange i ▸ hy)
    have hc := i.val.center_dist_top
    have ht := dist_triangle y i.val.center (z : Ambient d)
    rw [supportImmediateChild_radius μ R hR k z i] at hnear
    change dist y (z : Ambient d) ≤ 3 * latticeRadius R k
    linarith
  obtain ⟨g, hgLip, hgCover⟩ := exists_ball_lipschitz_cover_of_bounded_finite_family hn
    (257 ^ d) hcount (latticeRadius R k) hr (z : Ambient d) F (M / 64) hF hFImage
  obtain ⟨p, hpLip, hpRange, hpFix⟩ := exists_nonexpansive_retraction_of_complete_convex
    (closedBall (z : Ambient d) (2 * latticeRadius R k))
    ⟨(z : Ambient d), mem_closedBall_self (by positivity)⟩ isClosed_closedBall.isComplete
    (convex_closedBall (z : Ambient d) (2 * latticeRadius R k))
  have hcover (i : supportImmediateChildren μ R hR k z) (y : Ambient d)
      (hy : y ∈ i.val.cell) (hyRange : y ∈ Set.range (f i)) : y ∈ Set.range (p ∘ g) := by
    have htop := i.val.cell_subset_top hy
    have hball : y ∈ closedBall (z : Ambient d) (2 * latticeRadius R k) :=
      (supportLatticeCell_bounds μ R hR k z).2 htop.1
    have hyF : y ∈ Set.range (F i) := hFRange i ▸ hyRange
    obtain ⟨u, hu⟩ := hgCover (mem_iUnion.mpr ⟨i, hyF⟩)
    exact ⟨u, by change p (g u) = y; rw [hu, hpFix y hball]⟩
  have hsub : cleanSupportCell μ R hR k z \ Set.range (p ∘ g) ⊆
      ⋃ i : supportImmediateChildren μ R hR k z, i.val.cell \ Set.range (f i) := by
    intro y hy
    have hpart : y ∈ ⋃ i : supportImmediateChildren μ R hR k z, i.val.cell :=
      cleanSupportCell_eq_immediate_children μ R hR k z ▸ hy.1
    obtain ⟨i, hi⟩ := mem_iUnion.mp hpart
    exact mem_iUnion.mpr ⟨i, hi, fun h => hy.2 (hcover i y hi h)⟩
  refine ⟨p ∘ g, ?_, ?_, ?_, ?_⟩
  · simpa only [one_mul] using! hpLip.comp hgLip
  · rintro y ⟨u, rfl⟩
    exact hpRange (g u)
  · intro i y hy
    exact hcover i y hy.1 hy.2
  · have h : μ (cleanSupportCell μ R hR k z \ Set.range (p ∘ g)) ≤
        ∑' i : supportImmediateChildren μ R hR k z, μ (i.val.cell \ Set.range (f i)) :=
      (measure_mono hsub).trans (measure_iUnion_le _)
    simpa only [tsum_fintype] using! h

end

end RieszRectifiability

end OAI
