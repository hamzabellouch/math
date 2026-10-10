import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

theorem real_continuous_memLp_compact {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) : MemLp f 2 (volume.restrict K) :=
  (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    ((hf.pow 2).continuousOn.integrableOn_compact hK)

theorem real_toLp_norm_sq {X : Type*} [MeasurableSpace X] {m : Measure X}
    (f : X → ℝ) (hf : MemLp f 2 m) : ‖hf.toLp f‖^2 = ∫ x, (f x)^2 ∂m := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

end
end Yau

end OAI
