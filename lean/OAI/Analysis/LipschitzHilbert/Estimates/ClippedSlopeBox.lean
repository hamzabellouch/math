import OAI.Analysis.LipschitzHilbert.Estimates.TopDyadicDomination
import OAI.Analysis.LipschitzHilbert.Geometry.SlopeRectangle

namespace OAI

/-! Horizontal clipping before Euclidean enclosure. The width of the
clipped interval is bounded by both the testing strip and the original
dilation; no large horizontal dilation enters the long-side restriction. -/

noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert.SlopeBox

def clipLeft (T : SlopeBox) (D l : ℝ) : ℝ := max l (T.x-D*T.length)
def clipRight (T : SlopeBox) (D r : ℝ) : ℝ := min r (T.x+D*T.length)
def clipLength (T : SlopeBox) (D l r : ℝ) : ℝ := T.clipRight D r-T.clipLeft D l

def clipCenter (T : SlopeBox) (D l r : ℝ) : ℝ × ℝ :=
  let x := (T.clipLeft D l+T.clipRight D r)/2
  (x,T.y+T.slope*(x-T.x))

theorem clipLength_le_strip (T : SlopeBox) (D l r : ℝ) : T.clipLength D l r ≤ r-l := by
  unfold clipLength clipLeft clipRight
  linarith [min_le_left r (T.x+D*T.length), le_max_left l (T.x-D*T.length)]

theorem clipLength_le_dilation (T : SlopeBox) (D l r : ℝ) :
    T.clipLength D l r ≤ 2*D*T.length := by
  unfold clipLength clipLeft clipRight
  linarith [min_le_right r (T.x+D*T.length), le_max_right l (T.x-D*T.length)]

theorem clipped_coordinates (T : SlopeBox) (D l r : ℝ) (z : ℝ × ℝ)
    (hx : z.1 ∈ Icc l r) (hz : z ∈ T.radialDilation D) :
    |z.1-(T.clipCenter D l r).1| ≤ T.clipLength D l r/2 ∧
      |(z.2-(T.clipCenter D l r).2)-T.slope*(z.1-(T.clipCenter D l r).1)| ≤ D*T.width := by
  have hrad : |T.horizontal z|+|T.transverse z| ≤ D := hz
  have hx0 : |z.1-T.x| ≤ D*T.length := by
    have hb : |T.horizontal z| ≤ D := by linarith [abs_nonneg (T.transverse z)]
    rw [horizontal, abs_div, abs_of_pos T.length_pos] at hb
    exact (div_le_iff₀ T.length_pos).mp hb
  have hy0 : |(z.2-T.y)-T.slope*(z.1-T.x)| ≤ D*T.width := by
    have hb : |T.transverse z| ≤ D := by linarith [abs_nonneg (T.horizontal z)]
    rw [transverse, abs_div, abs_of_pos T.width_pos] at hb
    exact (div_le_iff₀ T.width_pos).mp hb
  have hleft : T.clipLeft D l ≤ z.1 := max_le hx.1 (by linarith [(abs_le.mp hx0).1])
  have hright : z.1 ≤ T.clipRight D r := le_min hx.2 (by linarith [(abs_le.mp hx0).2])
  constructor
  · dsimp [clipCenter, clipLength]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · convert hy0 using 2
    dsimp [clipCenter]
    ring

theorem clipLength_pos_of_positive_witness (T : SlopeBox) (D l r : ℝ)
    (E : Set (ℝ × ℝ)) (hpos : 0 < (volume.prod volume) E)
    (hE : ∀ z ∈ E, z.1 ∈ Icc l r ∧ z ∈ T.radialDilation D) :
    0 < T.clipLength D l r := by
  by_contra h
  have hlen : T.clipLength D l r ≤ 0 := le_of_not_gt h
  have hsub : E ⊆ {(T.clipCenter D l r).1} ×ˢ (univ : Set ℝ) := by
    intro z hz
    have hc := (T.clipped_coordinates D l r z (hE z hz).1 (hE z hz).2).1
    have heq : z.1 = (T.clipCenter D l r).1 := by
      have : |z.1-(T.clipCenter D l r).1| = 0 := by
        exact le_antisymm (by linarith) (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp this)
    exact ⟨heq,mem_univ _⟩
  have hnull : (volume.prod volume) ({(T.clipCenter D l r).1} ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.prod_prod]
    simp
  have hzero := (measure_mono hsub).trans_eq hnull
  exact (not_lt_of_ge hzero) hpos

end LipschitzHilbert.SlopeBox

end

end OAI
