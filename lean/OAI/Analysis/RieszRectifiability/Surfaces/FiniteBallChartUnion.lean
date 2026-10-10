import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.RescaledChildChartGluing
import OAI.Analysis.RieszRectifiability.Surfaces.BoundedNormalizedBallCharts
import OAI.Analysis.RieszRectifiability.Surfaces.FiniteChartParameterPacking

namespace OAI

/-!
# Finite unions of ball charts

Separated parameter islands encode finitely many bounded Lipschitz charts in a single
ball chart. The union constant combines the packing factor, the gluing estimate, and
the ambient Lipschitz extension constant. Extension followed by a nonexpansive
retraction also handles charts initially defined on subsets of the parameter ball.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

def finiteBallChartUnionConstant (d N : ℕ) (M : ℝ≥0) : ℝ≥0 :=
  lipschitzExtensionConstant (Ambient d) *
    separatedPatchGluingConstant (M * (4 * finiteChartPackingFactor N)) (finiteChartPackingFactor N) 0

theorem exists_ball_lipschitz_cover_of_finite_ball_charts {n d : ℕ} (hn : 0 < n)
    (N : ℕ) (r : ℝ) (hr : 0 < r) (z : Ambient d)
    (f : Fin N → ball (0 : Ambient n) r → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (f i))
    (himage : ∀ i, Set.range (f i) ⊆ closedBall z (3 * r)) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (finiteBallChartUnionConstant d N M) g ∧
      (⋃ i : Fin N, Set.range (f i)) ⊆ Set.range g := by
  have hdim : 0 < Module.finrank ℝ (Ambient n) := by simpa [Ambient] using! hn
  let : Nontrivial (Ambient n) := Module.nontrivial_of_finrank_pos hdim
  obtain ⟨e, he⟩ := exists_norm_eq (Ambient n) (show 0 ≤ (1 : ℝ) by norm_num)
  have hA : 0 < finiteChartPackingFactor N := by unfold finiteChartPackingFactor; positivity
  exact exists_ball_lipschitz_cover_of_rescaled_children (finiteChartParameterCenter e r N)
    (fun _ => z) (fun _ => r) f M (finiteChartPackingFactor N) 0 hA
    (finite_chart_parameter_centers_separated e he r hr N)
    (fun _ _ => by simp only [dist_self, NNReal.coe_zero, zero_mul, le_refl])
    himage hLip r (finite_chart_parameter_island_subset e he r hr N)

theorem exists_ball_lipschitz_cover_of_finite_partial_charts {n d : ℕ} (hn : 0 < n)
    (N : ℕ) (r : ℝ) (hr : 0 < r) (z : Ambient d)
    (D : Fin N → Set (Ambient n)) (hD : ∀ i, D i ⊆ ball (0 : Ambient n) r)
    (f : Fin N → Ambient n → Ambient d) (M : ℝ≥0)
    (hLip : ∀ i, LipschitzOnWith M (f i) (D i))
    (himage : ∀ i, f i '' D i ⊆ closedBall z (3 * r)) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (finiteBallChartUnionConstant d N (lipschitzExtensionConstant (Ambient d) * M)) g ∧
      (⋃ i : Fin N, f i '' D i) ⊆ Set.range g := by
  classical
  have hext (i : Fin N) := (hLip i).extend_finite_dimension
  choose F hF hEq using hext
  obtain ⟨p, hp, hpRange, hpFix⟩ := exists_nonexpansive_retraction_of_complete_convex
    (closedBall z (3 * r)) ⟨z, mem_closedBall_self (by positivity)⟩
    isClosed_closedBall.isComplete (convex_closedBall z (3 * r))
  let g : Fin N → ball (0 : Ambient n) r → Ambient d :=
    fun i => p ∘ (ball (0 : Ambient n) r).domRestrict (F i)
  have hgLip (i : Fin N) : LipschitzWith (lipschitzExtensionConstant (Ambient d) * M) (g i) := by
    simpa only [one_mul] using! hp.comp ((hF i).restrict (ball (0 : Ambient n) r))
  have hgRange (i : Fin N) : Set.range (g i) ⊆ closedBall z (3 * r) := by
    rintro y ⟨u, rfl⟩
    exact hpRange (F i u.val)
  obtain ⟨h, hhLip, hhCover⟩ := exists_ball_lipschitz_cover_of_finite_ball_charts hn N r hr z g
    (lipschitzExtensionConstant (Ambient d) * M) hgLip hgRange
  refine ⟨h, hhLip, ?_⟩
  intro y hy
  obtain ⟨i, u, hu, rfl⟩ := mem_iUnion.mp hy
  apply hhCover
  apply mem_iUnion.mpr
  refine ⟨i, ⟨u, hD i hu⟩, ?_⟩
  change p (F i u) = f i u
  rw [← hEq i hu, hpFix (f i u) (himage i (mem_image_of_mem (f i) hu))]

end

end RieszRectifiability

end OAI
