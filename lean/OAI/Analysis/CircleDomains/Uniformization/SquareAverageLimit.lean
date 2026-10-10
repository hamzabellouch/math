import OAI.Analysis.CircleDomains.Sobolev.CoordinateSquares
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Shrinking square averages recover the specified continuous representative. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def squareAverage (f : ℝ × ℝ → ℝ) (c : ℝ × ℝ) (r : ℝ) : ℝ :=
  ⨍ p in coordinateSquare c r, f p

lemma squareAverage_tendsto {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (c : ℝ × ℝ) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => squareAverage f c (r n)) atTop (𝓝 (f c)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hfd⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := c))
    (ε/2) (half_pos hε)
  have hev : ∀ᶠ n in atTop, r n < δ := (tendsto_order.mp hlim).2 δ hδ
  filter_upwards [hev] with n hn
  let : IsFiniteMeasure (volume.restrict (coordinateSquare c (r n))) :=
    isFiniteMeasure_restrict.mpr (coordinateSquare_compact c (r n)).measure_lt_top.ne
  let : NeZero (volume.restrict (coordinateSquare c (r n))) :=
    ⟨by simpa using coordinateSquare_volume_ne_zero c (hr n)⟩
  have hi : IntegrableOn f (coordinateSquare c (r n)) volume :=
    hf.continuousOn.integrableOn_compact (coordinateSquare_compact c (r n))
  have hb : ∀ᵐ p ∂volume.restrict (coordinateSquare c (r n)), |f c-f p| ≤ ε/2 := by
    filter_upwards [ae_restrict_mem (coordinateSquare_compact c (r n)).measurableSet] with p hp
    have hd : dist p c < δ := (mem_closedBall.mp hp).trans_lt hn
    simpa only [Real.dist_eq, abs_sub_comm] using (hfd hd).le
  have hbound := abs_sub_average_le_of_ae hi (f c) (ε/2) hb
  have hh : dist (squareAverage f c (r n)) (f c) ≤ ε/2 := by
    simpa only [squareAverage, Real.dist_eq, abs_sub_comm] using hbound
  exact hh.trans_lt (half_lt_self hε)

end CircleDomainRigidity

end

end OAI
