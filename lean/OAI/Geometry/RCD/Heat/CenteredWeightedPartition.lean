import OAI.Geometry.RCD.Heat.ScalingLogPartition

namespace OAI

/-! # Centering a positive weighted kernel integral -/

open MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)

theorem centered_weighted_log_partition (K G : Y → ℝ) (y₀ : Y) {ε : ℝ}
    (hε : 0 < ε) (hK : ∀ y, 0 < K y) (hG : ∀ y, 0 < G y)
    (hI : 0 < ∫ y, K y*G y ∂ν) :
    ε*Real.log (∫ y, K y*G y ∂ν)-ε*Real.log (G y₀) =
      ε*Real.log (∫ y, Real.exp ((ε*Real.log (K y)+
        ε*(Real.log (G y)-Real.log (G y₀)))/ε) ∂ν) := by
  have he (y : Y) : Real.exp ((ε*Real.log (K y)+
      ε*(Real.log (G y)-Real.log (G y₀)))/ε) = K y*G y/G y₀ := by
    have hh : (ε*Real.log (K y)+ε*(Real.log (G y)-Real.log (G y₀)))/ε =
        Real.log (K y)+Real.log (G y)-Real.log (G y₀) := by field_simp; ring
    rw [hh,Real.exp_sub,Real.exp_add,Real.exp_log (hK y),Real.exp_log (hG y),
      Real.exp_log (hG y₀)]
  simp only [he,integral_div,Real.log_div hI.ne' (hG y₀).ne']
  ring

end RegularPointCoordinates

end

end OAI
