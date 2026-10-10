import OAI.Geometry.NodalSets.Charts.CorrugationFrameOperatorBounds
import OAI.Geometry.NodalSets.Hausdorff.HausdorffDistortion

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal NNReal
noncomputable section

lemma frozenFrame_volume_lower (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    {c M A : ℝ} (hc : 0 < c) (hM : 0 < M)
    (hg : ∀ v : Coord, c*‖v‖^2 ≤ g v v) (hupper : ‖g‖ ≤ M)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (y : Coord) (s : Set Coord) (hs : ENNReal.ofReal A ≤ volume s) :
    ENNReal.ofReal (A/(M*(1+c⁻¹))^4) ≤ volume ((fun v ↦ y+e v) '' s) := by
  let K : ℝ≥0 := ⟨M*(1+c⁻¹),by positivity⟩
  have hK : 0 < K := by change 0 < M*(1+c⁻¹); positivity
  have hLip : LipschitzWith K (fun x : Coord ↦ e.symm (x-y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    simp only [dist_eq_norm,← map_sub,sub_sub_sub_cancel_right]
    exact frozenFrame_inverse_operator_bound g hc hM.le hg hupper e he (x-z)
  have hh := hLip.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 4)
    ((fun v ↦ y+e v) '' s)
  have himg : (fun x : Coord ↦ e.symm (x-y)) '' ((fun v ↦ y+e v) '' s) = s := by
    rw [← Set.image_comp]
    simp
  have hv : (Measure.hausdorffMeasure (4:ℝ) : Measure Coord) = volume := by
    simpa using hausdorffMeasure_pi_real (ι := Fin 4)
  rw [himg,hv] at hh
  have hh' : ENNReal.ofReal A ≤ (K:ℝ≥0∞)^4 * volume ((fun v ↦ y+e v) '' s) := by
    simpa using hs.trans hh
  exact ofReal_le_of_fourth_power_mul_le hK hh'

end
end Yau.Geometry

end OAI
