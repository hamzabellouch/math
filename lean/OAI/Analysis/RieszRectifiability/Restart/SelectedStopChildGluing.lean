import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.SelectedStopCoreGeometry
import OAI.Analysis.RieszRectifiability.Surfaces.ChildAndPointChartGluing

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_ball_lipschitz_cover_of_stop_children_and_survivors {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (E : Set (Ambient d)) (coord : Ambient d → Ambient n) (L : ℝ≥0) (hL : 1 ≤ L)
    (hcoord : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ (L : ℝ) * dist (coord x) (coord y))
    (ρ : ℝ) (hρ : 0 < ρ) (hcoordBall : ∀ x ∈ E, coord x ∈ closedBall (0 : Ambient n) ρ)
    (F : Set (SupportCellDescendant μ R hR k z)) (hF : F ⊆ cellRegionStops μ R hR k z Good)
    (x : F → Ambient d)
    (hx : ∀ i : F, x i ∈ closedBall i.val.center (i.val.radius / 32))
    (hxE : ∀ i : F, x i ∈ E) (hradius : ∀ i : F, i.val.radius ≤ ρ)
    (f : ∀ i : F, ball (0 : Ambient n) i.val.radius → Ambient d) (M : ℝ≥0)
    (hLip : ∀ i : F, LipschitzWith M (f i))
    (himage : ∀ i : F, Set.range (f i) ⊆ closedBall i.val.center (2 * i.val.radius)) :
    ∃ g : ball (0 : Ambient n) (2 * ρ) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) *
        separatedPatchGluingConstant (M * (4 * (32 * L))) (32 * L) L) g ∧
      ((cellRegionLimit μ R hR k z Good ∩ E) ∪ ⋃ i : F, Set.range (f i)) ⊆ Set.range g := by
  let P := cellRegionLimit μ R hR k z Good ∩ E
  let a : F → Ambient n := fun i => coord (x i)
  let b : P → Ambient n := fun y => coord y.val
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hA : 0 < 32 * L := by positivity
  have hsep (i j : F) (hij : i ≠ j) :
      i.val.radius + j.val.radius ≤ ((32 * L : ℝ≥0) : ℝ) * dist (a i) (a j) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using!
      stop_core_parameter_radii_separated μ R hR k z Good F hF x a L hx
        (fun i j => hcoord (x i) (hxE i) (x j) (hxE j)) i j hij
  have hcenter (i j : F) : dist (x i) (x j) ≤ (L : ℝ) * dist (a i) (a j) :=
    hcoord (x i) (hxE i) (x j) (hxE j)
  have hsepPoint (i : F) (y : P) :
      i.val.radius ≤ ((32 * L : ℝ≥0) : ℝ) * dist (a i) (b y) := by
    have hs := survivor_stop_core_point_radius_separation μ R hR k z Good
      i.val (hF i.property) (x i) y.val (hx i) y.property.1
    have hc := hcoord (x i) (hxE i) y.val y.property.2
    change i.val.radius ≤ (32 * (L : ℝ)) * dist (coord (x i)) (coord y.val)
    nlinarith [show 0 ≤ dist (x i) y.val from dist_nonneg]
  have hcenterPoint (i : F) (y : P) :
      dist (x i) y.val ≤ (L : ℝ) * dist (a i) (b y) :=
    hcoord (x i) (hxE i) y.val y.property.2
  have hpointLip (y w : P) : dist y.val w.val ≤ (L : ℝ) * dist (b y) (b w) :=
    hcoord y.val y.property.2 w.val w.property.2
  have himage' (i : F) : Set.range (f i) ⊆ closedBall (x i) (3 * i.val.radius) := by
    intro y hy
    have hc : dist y i.val.center ≤ 2 * i.val.radius := himage i hy
    have hx' : dist (x i) i.val.center ≤ i.val.radius / 32 := hx i
    have ht := dist_triangle y i.val.center (x i)
    rw [dist_comm i.val.center (x i)] at ht
    have hr := i.val.radius_pos
    change dist y (x i) ≤ 3 * i.val.radius
    linarith
  have hs : 1 ≤ 4 * (32 * L) := by nlinarith
  have hball (i : F) :
      ball (a i) (i.val.radius / (4 * (32 * (L : ℝ)))) ⊆ ball (0 : Ambient n) (2 * ρ) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using!
      small_parameter_ball_subset_double_ball (a i) ρ i.val.radius hρ
        (hcoordBall (x i) (hxE i)) (4 * (32 * L)) hs (hradius i)
  have hpointBall (y : P) : b y ∈ ball (0 : Ambient n) (2 * ρ) := by
    have h := hcoordBall y.val y.property.2
    change dist (coord y.val) (0 : Ambient n) ≤ ρ at h
    change dist (coord y.val) (0 : Ambient n) < 2 * ρ
    linarith
  obtain ⟨g, hg, hcover⟩ := exists_ball_lipschitz_cover_of_children_and_points
    a x (fun i => i.val.radius) b (fun y : P => y.val) f M (32 * L) L hA
    hsep hcenter hsepPoint hcenterPoint hpointLip himage' hLip (2 * ρ) hball hpointBall
  refine ⟨g, hg, ?_⟩
  intro y hy
  rcases hy with hp | hc
  · exact hcover (Or.inr ⟨⟨y, hp⟩, rfl⟩)
  · exact hcover (Or.inl hc)

end

end RieszRectifiability

end OAI
