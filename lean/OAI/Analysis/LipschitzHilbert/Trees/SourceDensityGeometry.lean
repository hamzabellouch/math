import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityKeepers
import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineNesting

namespace OAI

/-! Actual geometry behind the density keeper assignment: intersecting
angular cells give slope control, and intersecting slope boxes then give
the required spatial enlargement. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem densitySpatialBox_measurable (T : SlopeBox) (K : ℝ) :
    MeasurableSet (densitySpatialBox T K) := by
  change MeasurableSet ({z : ℝ×ℝ | |z.1-T.x| ≤ K*T.length} ∩
    {z : ℝ×ℝ | |(z.2-T.y)-T.slope*(z.1-T.x)| ≤ K*T.width})
  exact (isClosed_le ((continuous_fst.sub continuous_const).abs) continuous_const).measurableSet.inter
    (isClosed_le (((continuous_snd.sub continuous_const).sub
      (continuous_const.mul (continuous_fst.sub continuous_const))).abs) continuous_const).measurableSet

theorem densityTest_measurable {E : Set (ℝ×ℝ)} {u : ℝ×ℝ → ℝ}
    {omega : Set ℝ} (hE : MeasurableSet E) (hu : Measurable u)
    (homega : MeasurableSet omega) (T : SlopeBox) (K : ℝ) :
    MeasurableSet (densityTest E u T omega K) :=
  (hE.inter (densitySpatialBox_measurable T K)).inter (hu homega)

theorem density_center_in_keeper (T S : SlopeBox) {K C : ℝ}
    (hK : 0 ≤ K) (hlen : T.length ≤ S.length) (hwidth : T.width = S.width)
    (hslope : |T.slope-S.slope| * T.length ≤ C*S.width)
    {z : ℝ×ℝ} (hT : z ∈ densitySpatialBox T K) (hS : z ∈ densitySpatialBox S K) :
    |T.x-S.x| ≤ 2*K*S.length ∧
      |(T.y-S.y)-S.slope*(T.x-S.x)| ≤ (2+C)*K*S.width := by
  have hx : |T.x-S.x| ≤ 2*K*S.length := by
    calc
      _ = |(z.1-S.x)-(z.1-T.x)| := by congr 1; ring
      _ ≤ |z.1-S.x|+|z.1-T.x| := abs_sub _ _
      _ ≤ K*S.length+K*T.length := add_le_add hS.1 hT.1
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlen hK]
  refine ⟨hx,?_⟩
  have hp : |T.slope-S.slope| * |z.1-T.x| ≤ C*K*S.width := by
    calc
      _ ≤ |T.slope-S.slope| * (K*T.length) :=
        mul_le_mul_of_nonneg_left hT.1 (abs_nonneg _)
      _ = K*(|T.slope-S.slope| * T.length) := by ring
      _ ≤ K*(C*S.width) := mul_le_mul_of_nonneg_left hslope hK
      _ = _ := by ring
  calc
    _ = |((z.2-S.y)-S.slope*(z.1-S.x)) -
        ((z.2-T.y)-T.slope*(z.1-T.x)) - (T.slope-S.slope)*(z.1-T.x)| := by
      congr 1
      ring
    _ ≤ |(z.2-S.y)-S.slope*(z.1-S.x)|+
        |(z.2-T.y)-T.slope*(z.1-T.x)|+|(T.slope-S.slope)*(z.1-T.x)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ K*S.width+K*T.width+C*K*S.width := by
      rw [abs_mul]
      exact add_le_add (add_le_add hS.2 hT.2) hp
    _ = _ := by rw [hwidth]; ring

theorem density_box_subset_keeper (T S : SlopeBox) {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hlen : T.length ≤ S.length)
    (hwidth : T.width = S.width)
    (hslope : |T.slope-S.slope| * T.length ≤ C*S.width)
    (hinter : (densitySpatialBox T K ∩ densitySpatialBox S K).Nonempty) :
    densitySpatialBox T K ⊆ densitySpatialBox S ((3+2*C)*K) := by
  obtain ⟨q,hqT,hqS⟩ := hinter
  obtain ⟨hcx,hcy⟩ := density_center_in_keeper T S hK hlen hwidth hslope hqT hqS
  intro z hz
  have hx : |z.1-S.x| ≤ 3*K*S.length := by
    calc
      _ = |(z.1-T.x)+(T.x-S.x)| := by congr 1; ring
      _ ≤ |z.1-T.x|+|T.x-S.x| := abs_add_le _ _
      _ ≤ K*T.length+2*K*S.length := add_le_add hz.1 hcx
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlen hK]
  have hp : |T.slope-S.slope| * |z.1-T.x| ≤ C*K*S.width := by
    calc
      _ ≤ |T.slope-S.slope| * (K*T.length) :=
        mul_le_mul_of_nonneg_left hz.1 (abs_nonneg _)
      _ = K*(|T.slope-S.slope| * T.length) := by ring
      _ ≤ K*(C*S.width) := mul_le_mul_of_nonneg_left hslope hK
      _ = _ := by ring
  constructor
  · exact hx.trans (by nlinarith [mul_nonneg (mul_nonneg hC hK) S.length_pos.le])
  · calc
      _ = |((z.2-T.y)-T.slope*(z.1-T.x)) +
          ((T.y-S.y)-S.slope*(T.x-S.x)) + (T.slope-S.slope)*(z.1-T.x)| := by
        congr 1
        ring
      _ ≤ |(z.2-T.y)-T.slope*(z.1-T.x)|+
          |(T.y-S.y)-S.slope*(T.x-S.x)|+|(T.slope-S.slope)*(z.1-T.x)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ K*T.width+(2+C)*K*S.width+C*K*S.width := by
        rw [abs_mul]
        exact add_le_add (add_le_add hz.2 hcy) hp
      _ = _ := by rw [hwidth]; ring

theorem density_angular_cell_slope {q k l i j : ℤ} {s t : ℝ}
    (hlk : l ≤ k) (hinter : (DyadicLineGrid.cell q k i ∩ DyadicLineGrid.cell q l j).Nonempty)
    (hs : s ∈ DyadicLineGrid.cell q k i) (ht : t ∈ DyadicLineGrid.cell q l j) :
    |s-t| ≤ DyadicLineGrid.scale k := by
  have ht' := DyadicLineGrid.cell_subset_of_intersect hlk
    (by simpa only [inter_comm] using hinter) ht
  have hnext : DyadicLineGrid.left q k (i+1) =
      DyadicLineGrid.left q k i+DyadicLineGrid.scale k := by
    unfold DyadicLineGrid.left
    push_cast
    ring
  change DyadicLineGrid.left q k i ≤ s ∧ s < DyadicLineGrid.left q k (i+1) at hs
  change DyadicLineGrid.left q k i ≤ t ∧ t < DyadicLineGrid.left q k (i+1) at ht'
  rw [hnext] at hs ht'
  exact abs_le.mpr ⟨by linarith [hs.1,ht'.2],by linarith [hs.2,ht'.1]⟩

end LipschitzHilbert

end

end OAI
