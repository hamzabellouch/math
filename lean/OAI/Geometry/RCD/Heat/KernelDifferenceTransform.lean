import OAI.Geometry.RCD.Heat.ContinuousKernelContraction

namespace OAI

/-! # Positive kernel maps on the space of continuous differences -/

open Set MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [CompactSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure Y) [IsProbabilityMeasure μ]

def kernelDifferenceTransform (K : C(X × Y, ℝ)) {m : ℝ} (hm : 0 < m)
    (hK : ∀ x y, m ≤ K (x,y)) (y₀ : Y) (d : ContinuousDifference Y) :
    ContinuousDifference X :=
  continuousDifference X (-continuousKernelLog μ K hm hK (differenceValue Y d y₀))

theorem kernelDifferenceTransform_norm [Nonempty Y] (K : C(X × Y, ℝ)) {m M : ℝ}
    (hm : 0 < m) (hK : ∀ x y, m ≤ K (x,y)) (hM : ∀ x y, K (x,y) ≤ M)
    (y₀ : Y) (d e : ContinuousDifference Y) (hMm : m ≤ M) :
    ‖kernelDifferenceTransform μ K hm hK y₀ d - kernelDifferenceTransform μ K hm hK y₀ e‖ ≤
      (1-m/M)*‖d-e‖ := by
  have hM0 : 0 < M := hm.trans_le hMm
  have hq : 0 ≤ 1-m/M := sub_nonneg.mpr ((div_le_one hM0).mpr hMm)
  apply ContinuousDifference.norm_le X (mul_nonneg hq (norm_nonneg _))
  intro x z
  have hh := continuousKernelLog_pair_bound μ K hm hK hM
    (differenceValue Y d y₀) (differenceValue Y e y₀) (C := ‖d-e‖) (fun y w => ?_) x z
  · convert hh using 1
    · change |(-continuousKernelLog μ K hm hK (differenceValue Y d y₀) x -
            -continuousKernelLog μ K hm hK (differenceValue Y d y₀) z) -
          (-continuousKernelLog μ K hm hK (differenceValue Y e y₀) x -
            -continuousKernelLog μ K hm hK (differenceValue Y e y₀) z)| = _
      rw [show (-continuousKernelLog μ K hm hK (differenceValue Y d y₀) x -
            -continuousKernelLog μ K hm hK (differenceValue Y d y₀) z) -
          (-continuousKernelLog μ K hm hK (differenceValue Y e y₀) x -
            -continuousKernelLog μ K hm hK (differenceValue Y e y₀) z) =
          -((continuousKernelLog μ K hm hK (differenceValue Y d y₀) x -
            continuousKernelLog μ K hm hK (differenceValue Y e y₀) x) -
            (continuousKernelLog μ K hm hK (differenceValue Y d y₀) z -
            continuousKernelLog μ K hm hK (differenceValue Y e y₀) z)) by ring,abs_neg]
    · rfl
  · rw [show (differenceValue Y d y₀ y - differenceValue Y e y₀ y) -
        (differenceValue Y d y₀ w - differenceValue Y e y₀ w) =
        (differenceValue Y d y₀ y - differenceValue Y d y₀ w) - (differenceValue Y e y₀ y - differenceValue Y e y₀ w) by ring,
      differenceValue_sub Y d y₀ y w,differenceValue_sub Y e y₀ y w]
    exact (d-e).val.norm_coe_le_norm (y,w)

end RegularPointCoordinates

end

end OAI
