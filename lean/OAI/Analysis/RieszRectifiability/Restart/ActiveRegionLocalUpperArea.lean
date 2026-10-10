import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionZeroLocalArea
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLocalPositiveCharge
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLocalChartArea
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionHighScaleLocalArea

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionLocalUpperAreaConstant (n d : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  activeRegionZeroLocalAreaConstant n C G +
    activeRegionSmallScaleAreaConstant n d C * ENNReal.ofReal G * (2 : ℝ≥0∞) ^ n +
    planeChartBallAreaConstant n 16 64 * (2 : ℝ≥0∞) ^ n +
    planeChartBallAreaConstant n 4 16

theorem activeRegionLocalUpperAreaConstant_lt_top (n d : ℕ) (C G : ℝ) :
    activeRegionLocalUpperAreaConstant n d C G < ⊤ := by
  have hz := activeRegionZeroLocalAreaConstant_lt_top n C G
  have hs := activeRegionSmallScaleAreaConstant_lt_top n d C
  have hp := planeChartBallAreaConstant_lt_top n 16 64
  have hh := planeChartBallAreaConstant_lt_top n 4 16
  unfold activeRegionLocalUpperAreaConstant
  finiteness

theorem active_region_far_positive_scale_portion_area_le {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (r : ℝ) (hr : 0 < r) (A : Set (Ambient d))
    (hA : A ⊆ Set.range f ∩ closedBall p r)
    (hD : ∀ x ∈ A, 32 * r < cellRegionStoppingScale μ R hR k z Good x ∧
      cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + 1)) :
    (μH[(n : ℝ)] : Measure (Ambient d)) A ≤
      (planeChartBallAreaConstant n 16 64 * (2 : ℝ≥0∞) ^ n) * (ENNReal.ofReal r) ^ n := by
  by_cases hempty : A = ∅
  · rw [hempty, measure_empty]
    exact zero_le
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  have hxD := hD x hx
  have hsub : A ⊆ Set.range f ∩ closedBall x (2 * r) := by
    intro y hy
    refine ⟨(hA hy).1, ?_⟩
    have hxp : dist x p ≤ r := (hA hx).2
    have hyp : dist y p ≤ r := (hA hy).2
    have ht := dist_triangle_right y x p
    change dist y x ≤ 2 * r
    linarith
  have harea := active_region_positive_scale_local_ball_area_le μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel x (by linarith) hxD.2 (2 * r) (by positivity) (by linarith)
  calc
    _ ≤ (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall x (2 * r)) := measure_mono hsub
    _ ≤ planeChartBallAreaConstant n 16 64 * (ENNReal.ofReal (2 * r)) ^ n := harea
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_pow]
      ring

theorem active_region_limit_local_ball_area_le {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (r : ℝ) (hr : 0 < r) :
    (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) ≤
      activeRegionLocalUpperAreaConstant n d C G * (ENNReal.ofReal r) ^ n := by
  let D := cellRegionStoppingScale μ R hR k z Good
  let T := Set.range f ∩ closedBall p r
  let Z := cellRegionZeroSet μ R hR k z Good ∩ closedBall p r
  let A := T ∩ {x | 0 < D x ∧ D x < latticeRadius R (k + 1) ∧ D x ≤ 32 * r}
  let B := T ∩ {x | 32 * r < D x ∧ D x < latticeRadius R (k + 1)}
  let H := closedBall p r ∩ {x | latticeRadius R (k + 1) ≤ D x}
  have hεtiny : ε ≤ 1 / 268435456 := by linarith
  have hz := active_region_zero_local_ball_area_le μ C G hC hG hg hlower R hR k hcore z Good p r hr
  have ha := active_region_local_positive_scale_area_charge μ C hC hlower R hR k hcore z Good S hS
    ε hε hεfine hsmall hfit f hmodel p r hr A (fun _ hx => hx.1)
    (fun _ hx => hx.2.2.2) (fun _ hx => ⟨hx.2.1, hx.2.2.1⟩)
  have hμ := hg.2 p (2 * r) (by positivity)
  have ha' : (μH[(n : ℝ)] : Measure (Ambient d)) A ≤
      (activeRegionSmallScaleAreaConstant n d C * ENNReal.ofReal G * (2 : ℝ≥0∞) ^ n) *
        (ENNReal.ofReal r) ^ n := by
    calc
      _ ≤ activeRegionSmallScaleAreaConstant n d C * μ (ball p (2 * r)) := ha
      _ ≤ activeRegionSmallScaleAreaConstant n d C * ENNReal.ofReal (G * (2 * r) ^ n) :=
        mul_le_mul_right hμ _
      _ = _ := by
        rw [ENNReal.ofReal_mul hG.le, ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * r),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_pow]
        ring
  have hb := active_region_far_positive_scale_portion_area_le μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel p r hr B (fun _ hx => hx.1) (fun _ hx => hx.2)
  have hh := active_region_high_scale_local_ball_area_le μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel p r hr H inter_subset_left (fun _ hx => hx.2)
  have hcover : T ⊆ ((Z ∪ A) ∪ B) ∪ (Set.range f ∩ H) := by
    intro x hx
    by_cases hhigh : latticeRadius R (k + 1) ≤ D x
    · exact Or.inr ⟨hx.1, hx.2, hhigh⟩
    have hbelow : D x < latticeRadius R (k + 1) := lt_of_not_ge hhigh
    by_cases hzero : D x = 0
    · exact Or.inl (Or.inl (Or.inl ⟨hzero, hx.2⟩))
    have hnonneg : 0 ≤ D x := cellRegionStoppingScale_nonneg μ R hR k z Good x
    have hpos : 0 < D x := lt_of_le_of_ne hnonneg (Ne.symm hzero)
    by_cases hnear : D x ≤ 32 * r
    · exact Or.inl (Or.inl (Or.inr ⟨hx, hpos, hbelow, hnear⟩))
    · exact Or.inl (Or.inr ⟨hx, lt_of_not_ge hnear, hbelow⟩)
  calc
    _ ≤ (μH[(n : ℝ)] : Measure (Ambient d)) (((Z ∪ A) ∪ B) ∪ (Set.range f ∩ H)) := measure_mono hcover
    _ ≤ (((μH[(n : ℝ)] : Measure (Ambient d)) Z + (μH[(n : ℝ)] : Measure (Ambient d)) A) +
        (μH[(n : ℝ)] : Measure (Ambient d)) B) +
        (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ H) :=
      (measure_union_le _ _).trans
        (add_le_add ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ ((activeRegionZeroLocalAreaConstant n C G * (ENNReal.ofReal r) ^ n +
        (activeRegionSmallScaleAreaConstant n d C * ENNReal.ofReal G * (2 : ℝ≥0∞) ^ n) *
          (ENNReal.ofReal r) ^ n) +
        (planeChartBallAreaConstant n 16 64 * (2 : ℝ≥0∞) ^ n) * (ENNReal.ofReal r) ^ n) +
        planeChartBallAreaConstant n 4 16 * (ENNReal.ofReal r) ^ n :=
      add_le_add (add_le_add (add_le_add hz ha') hb) hh
    _ = _ := by unfold activeRegionLocalUpperAreaConstant; ring

end

end RieszRectifiability

end OAI
