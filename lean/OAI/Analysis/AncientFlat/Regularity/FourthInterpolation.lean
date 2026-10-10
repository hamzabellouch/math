import OAI.Analysis.AncientFlat.Regularity.InterpolationEpsilon

namespace OAI
noncomputable section
open Set Filter Metric ParabolicInterior
open scoped ContDiff
namespace ParabolicInterpolation
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem fourth_sup_epsilon (α ε r R : ℝ) (hα : 0<α) (hε : 0<ε) (hrR : r<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (f : V → E), ContDiff ℝ 4 f → ∀ (U H : ℝ), 0≤U → 0≤H →
      (∀ x, ‖x‖<R → ‖f x‖≤U) →
      (∀ x, ‖x‖<R → ∀ y, ‖y‖<R →
        ‖iteratedFDeriv ℝ 4 f x-iteratedFDeriv ℝ 4 f y‖≤H*‖x-y‖^α) →
      ∀ x, ‖x‖<r → ‖iteratedFDeriv ℝ 4 f x‖≤ε*H+C*U := by
  have h4 : 0<(4:ℝ)^α := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨q,hq,_,hgap,hsmall⟩ := exists_interpolation_scale (1-α) (ε/(4:ℝ)^α) (R-r)
    (by linarith) (div_pos hε h4) (sub_pos.mpr hrR)
  rw [show 1-(1-α)=α by ring] at hsmall
  have hs : (4*q)^α≤ε := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) hq.le]
    have hqα : 0≤q^α := Real.rpow_nonneg hq.le _
    have hb : q^α≤ε/(4:ℝ)^α := by linarith
    have := (le_div_iff₀ h4).mp hb
    simpa only [mul_comm] using this
  refine ⟨16/q^4,by positivity,?_⟩
  intro f hf U H hU hH hu hD x hx
  have hb := fourth_sup_interpolation f hf x R q U H α hq hU hH hα.le (by linarith) hu hD
  calc
    _≤16/q^4*U+H*(4*q)^α := hb
    _≤16/q^4*U+H*ε := add_le_add le_rfl (mul_le_mul_of_nonneg_left hs hH)
    _=_ := by ring
end ParabolicInterpolation

end

end OAI
