import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.GlobalGrowth
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionStopCoreLowerArea

namespace OAI

/-!
# Stopping-cell mass controlled by model area

Global growth bounds and the lower area of stopping cores control the mass of
stopping cells by Hausdorff measure on the limit model. Disjoint cores allow these
estimates to be summed over countable families inside a prescribed region.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionStopMassAreaConstant (n : ℕ) (G : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (G * 384 ^ n) / activeRegionPositiveLocalLowerAreaConstant n

theorem activeRegionStopMassAreaConstant_lt_top (n : ℕ) (G : ℝ) :
    activeRegionStopMassAreaConstant n G < ⊤ := by
  exact ENNReal.div_lt_top ENNReal.ofReal_ne_top
    (activeRegionPositiveLocalLowerAreaConstant_pos n).ne'

theorem cellRegionStops_small_cores_pairwise_disjoint {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    (cellRegionStops μ R hR k z Good).Pairwise
      (fun i j => Disjoint (closedBall i.center (i.radius / 32))
        (closedBall j.center (j.radius / 32))) := by
  intro i hi j hj hne
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hs := cellRegionStops_centers_separated μ R hR k z Good i j hi hj hne
  have hi' := (le_max_left i.radius j.radius).trans hs
  have hj' := (le_max_right i.radius j.radius).trans hs
  have ht := dist_triangle i.center x j.center
  rw [dist_comm i.center x] at ht
  have hxi' : dist x i.center ≤ i.radius / 32 := hxi
  have hxj' : dist x j.center ≤ j.radius / 32 := hxj
  have hr := i.radius_pos
  linarith

variable {n d : ℕ} (μ : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth n G μ)
  (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hg hε hεfine hsmall hfit hmodel

theorem active_region_stop_cell_mass_le_core_area
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (hdepth : 0 < i.depth) :
    μ i.cell ≤ activeRegionStopMassAreaConstant n G *
      (μH[(n : ℝ)] : Measure (Ambient d))
        (Set.range f ∩ closedBall i.center (i.radius / 32)) := by
  have hri := i.radius_pos
  have hGnonneg : 0 ≤ G := hg.1
  have hupper : μ i.cell ≤ ENNReal.ofReal (G * 384 ^ n) *
      (ENNReal.ofReal (i.radius / 128)) ^ n := by
    calc
      _ ≤ μ (ball i.center (3 * i.radius)) := measure_mono (fun x hx => by
        have h := i.dist_center_of_mem x hx
        change dist x i.center < 3 * i.radius
        linarith)
      _ ≤ ENNReal.ofReal (G * (3 * i.radius) ^ n) := hg.2 i.center _ (by positivity)
      _ = _ := by
        rw [show 3 * i.radius = 384 * (i.radius / 128) by ring, mul_pow, ← mul_assoc,
          ENNReal.ofReal_mul (by positivity : 0 ≤ G * 384 ^ n),
          ENNReal.ofReal_pow (by positivity : 0 ≤ i.radius / 128)]
  have harea := active_region_stop_core_area_ge μ R hR k z Good S hS ε hε hεfine
    hsmall hfit f hmodel i hi hdepth
  calc
    _ ≤ ENNReal.ofReal (G * 384 ^ n) * (ENNReal.ofReal (i.radius / 128)) ^ n := hupper
    _ = activeRegionStopMassAreaConstant n G *
        (activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal (i.radius / 128)) ^ n) := by
      unfold activeRegionStopMassAreaConstant
      rw [← mul_assoc, ENNReal.div_mul_cancel
        (activeRegionPositiveLocalLowerAreaConstant_pos n).ne'
        (activeRegionPositiveLocalLowerAreaConstant_lt_top n).ne]
    _ ≤ _ := mul_le_mul_right harea _

theorem active_region_stop_subfamily_mass_le_area
    (F : Set (SupportCellDescendant μ R hR k z))
    (hF : F ⊆ cellRegionStops μ R hR k z Good) (hdepth : ∀ i ∈ F, 0 < i.depth)
    (Ω : Set (Ambient d))
    (hΩ : ∀ i ∈ F, closedBall i.center (i.radius / 32) ⊆ Ω) :
    (∑' i : F, μ i.val.cell) ≤ activeRegionStopMassAreaConstant n G *
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ Ω) := by
  let := supportCellDescendant_countable μ R hR k z
  let A := fun i : F => Set.range f ∩ closedBall i.val.center (i.val.radius / 32)
  have hclosed : IsClosed (Set.range f) := by
    simpa only [Set.image_univ] using! hmodel.2.1.isClosedMap Set.univ isClosed_univ
  have hm : ∀ i : F, MeasurableSet (A i) :=
    fun _ => hclosed.measurableSet.inter isClosed_closedBall.measurableSet
  have hd : Pairwise (fun i j : F => Disjoint (A i) (A j)) := by
    intro i j hij
    have h := cellRegionStops_small_cores_pairwise_disjoint μ R hR k z Good
      (hF i.property) (hF j.property) (fun heq => hij (Subtype.ext heq))
    exact h.mono inter_subset_right inter_subset_right
  have hs : (⋃ i : F, A i) ⊆ Set.range f ∩ Ω := by
    apply iUnion_subset
    intro i x hx
    exact ⟨hx.1, hΩ i.val i.property hx.2⟩
  calc
    _ ≤ ∑' i : F, activeRegionStopMassAreaConstant n G *
        (μH[(n : ℝ)] : Measure (Ambient d)) (A i) :=
      ENNReal.tsum_le_tsum (fun i => active_region_stop_cell_mass_le_core_area
        μ G hg R hR k z Good S hS ε hε hεfine hsmall hfit f hmodel i.val
          (hF i.property) (hdepth i.val i.property))
    _ = activeRegionStopMassAreaConstant n G *
        (μH[(n : ℝ)] : Measure (Ambient d)) (⋃ i : F, A i) := by
      rw [ENNReal.tsum_mul_left, measure_iUnion hd hm]
    _ ≤ _ := mul_le_mul_right (measure_mono hs) _

end

end RieszRectifiability

end OAI
