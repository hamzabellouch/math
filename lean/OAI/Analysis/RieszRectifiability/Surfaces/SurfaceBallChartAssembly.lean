import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.NativeSurfaceArea
import OAI.Analysis.RieszRectifiability.Surfaces.SurfaceBallCellMass
import OAI.Analysis.RieszRectifiability.Nets.FiniteFamilyRetractionCover

namespace OAI

/-!
# Assembling surface ball charts

Finite cell charts combine into a ball chart whose uncovered surface mass is
controlled by the sum of the cell deficits. Restriction to the surface identifies
this deficit with the corresponding Hausdorff measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_surface_ball_chart_of_cell_deficits {n d : ℕ} (hn : 0 < n)
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ s : ℝ, AdmissibleRadius ν s →
      ENNReal.ofReal (s ^ n / C) ≤ ν (ball x s))
    (r : ℝ) (hr : 0 < r) (a : Ambient d) (M : ℝ≥0) (loss : ℝ≥0∞)
    (hcharts : ∀ z : surfaceBallCellCenters ν r hr a,
      ∃ g : ball (0 : Ambient n) r → Ambient d, LipschitzWith M g ∧
        ν (cleanSupportCell ν r hr 0 z.val \ Set.range g) ≤ loss * ν (cleanSupportCell ν r hr 0 z.val)) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (finiteBallChartUnionConstant d (11 ^ d) M) g ∧
      Set.range g ⊆ closedBall a (3 * r) ∧
      (μH[(n : ℝ)] : Measure (Ambient d)) ((A ∩ closedBall a (3 * r)) \ Set.range g) ≤
        loss * ENNReal.ofReal (G * (8 * r) ^ n) := by
  classical
  let F := surfaceBallCellCenters ν r hr a
  choose child hLip hLoss using hcharts
  have hN : Fintype.card F ≤ 11 ^ d := by
    simpa only [Fintype.card_coe] using! surfaceBallCellCenters_card_le ν r hr a
  obtain ⟨g, hglip, hgrange, hcover⟩ := exists_bounded_ball_cover_of_finite_family hn
    (11 ^ d) hN r hr a child M hLip
  let B := supportLatticeExceptional ν r hr
  have hB : ν B = 0 := supportLatticeExceptional_null ν C G hC hG hg hlower r hr
  have hsub : ((A ∩ closedBall a (3 * r)) \ Set.range g) ⊆
      B ∪ ⋃ z : F, cleanSupportCell ν r hr 0 z.val \ Set.range (child z) := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inl hxB
    have hxν : x ∈ ν.support := hsupport.symm ▸ hx.1.1
    obtain ⟨z, hz, hcell⟩ := surface_ball_covered_by_selected_cells_off_exceptional
      ν r hr a x ⟨hxν, hx.1.2⟩ hxB
    refine Or.inr (mem_iUnion.mpr ⟨⟨z, hz⟩, hcell, ?_⟩)
    intro h
    exact hx.2 (hcover ⟨z, hz⟩ ⟨hx.1.2, h⟩)
  have hEq : (μH[(n : ℝ)] : Measure (Ambient d)) ((A ∩ closedBall a (3 * r)) \ Set.range g) =
      ν ((A ∩ closedBall a (3 * r)) \ Set.range g) := by
    rw [hν]
    exact ((μH[(n : ℝ)] : Measure (Ambient d)).restrict_eq_self
      (sdiff_subset.trans inter_subset_left)).symm
  refine ⟨g, hglip, hgrange, ?_⟩
  rw [hEq]
  calc
    _ ≤ ν (B ∪ ⋃ z : F, cleanSupportCell ν r hr 0 z.val \ Set.range (child z)) := measure_mono hsub
    _ ≤ ν B + ν (⋃ z : F, cleanSupportCell ν r hr 0 z.val \ Set.range (child z)) := measure_union_le _ _
    _ = ν (⋃ z : F, cleanSupportCell ν r hr 0 z.val \ Set.range (child z)) := by rw [hB, zero_add]
    _ ≤ ∑ z : F, ν (cleanSupportCell ν r hr 0 z.val \ Set.range (child z)) := by
      simpa only [tsum_fintype] using! (measure_iUnion_le
        (fun z : F => cleanSupportCell ν r hr 0 z.val \ Set.range (child z)) (μ := ν))
    _ ≤ ∑ z : F, loss * ν (cleanSupportCell ν r hr 0 z.val) := Finset.sum_le_sum (fun z _ => hLoss z)
    _ = loss * ∑ z : F, ν (cleanSupportCell ν r hr 0 z.val) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul' le_rfl (surface_ball_cell_mass_sum_le ν G hg r hr a)

end

end RieszRectifiability

end OAI
