import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicMeasureCalculus
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

/-! # Scaling the logarithmic measure below a moving upper endpoint -/
namespace JointDickman
open MeasureTheory Set

 theorem logarithmicPrimeMeasure_restrict_Iic {c u : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) :
    (logarithmicPrimeMeasure c : Measure ℝ).restrict (Iic u) =
      Measure.map Real.exp (volume.restrict (Ioc (Real.log c) (Real.log u))) := by
  change (Measure.map Real.exp (volume.restrict (Ioc (Real.log c) 0))).restrict (Iic u) = _
  rw [Measure.restrict_map Real.measurable_exp measurableSet_Iic, Measure.restrict_restrict]
  · congr 2
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc, ← Real.le_log_iff_exp_le hu]
    constructor
    · rintro ⟨htu, hct, _⟩
      exact ⟨hct, htu⟩
    · rintro ⟨hct, htu⟩
      exact ⟨htu, hct, htu.trans (Real.log_nonpos hu.le hu1)⟩
  · exact Real.measurable_exp measurableSet_Iic

 theorem logarithmicPrimeMeasure_scale {c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) (hu1 : u ≤ 1) :
    Measure.map (fun t : ℝ => t/u)
      ((logarithmicPrimeMeasure c : Measure ℝ).restrict (Iic u)) =
        (logarithmicPrimeMeasure (c/u) : Measure ℝ) := by
  rw [logarithmicPrimeMeasure_restrict_Iic hu hu1,
    Measure.map_map (by fun_prop : Measurable (fun t : ℝ => t/u)) Real.measurable_exp]
  have hp : (fun t : ℝ => t-Real.log u) ⁻¹' Ioc (Real.log (c/u)) 0 =
      Ioc (Real.log c) (Real.log u) := by
    ext t
    simp only [mem_preimage, mem_Ioc, Real.log_div hc.ne' hu.ne']
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hm := (measurePreserving_sub_right (volume : Measure ℝ) (Real.log u)).restrict_preimage
    (s := Ioc (Real.log (c/u)) 0) measurableSet_Ioc
  rw [hp] at hm
  change Measure.map (fun t : ℝ => Real.exp t/u) _ =
    Measure.map Real.exp (volume.restrict (Ioc (Real.log (c/u)) 0))
  rw [← hm.map_eq, Measure.map_map Real.measurable_exp (by fun_prop : Measurable (fun t : ℝ => t-Real.log u))]
  congr 1
  funext t
  simp [Real.exp_sub, Real.exp_log hu]

end JointDickman

end OAI
