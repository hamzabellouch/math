import Mathlib
import OAI.Geometry.PrescribedRicci.DiscreteInterpolation
import OAI.Geometry.PrescribedRicci.InterpolationExponents
import OAI.Geometry.PrescribedRicci.JetInterpolation

namespace OAI

/-! Jet Tame Product. -/

section

 

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace TameInterpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma jet_exponent_recurrence (e : ι → E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (m : ℕ) (hm : 0 < m)
    (j : ℕ) (hj : j+2 ≤ m) :
    (jetNorm e f (j+1) (exponent m (j+1)))^2 ≤
    (2*(m:ℝ))*jetNorm e f j (exponent m j)*jetNorm e f (j+2) (exponent m (j+2)) := by
  let p : ℝ := 2*(m:ℝ)/((j+1:ℕ):ℝ)
  have hp : 2 < p := exponent_middle_gt (by omega : j+1 < m)
  let := exponent_holder_step (by omega : j+1 < m)
  let := interpolation_holder_conjugate hp
  have h := jetNorm_step e hf hc j hp (exponent m j) (exponent m (j+2))
    (ENNReal.ofReal ((p-2)/p))⁻¹ (ENNReal.ofReal (2/p))⁻¹ (interpolation_power_exponent hp)
  rw [exponent_of_pos hm (by omega : 0 < j+1)]
  apply h.trans
  have hpm : p ≤ 2*(m:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < ((j+1:ℕ):ℝ))).mpr
    have hj1 : (1:ℝ) ≤ ((j+1:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ j+1)
    nlinarith only [hj1,Nat.cast_nonneg (α:=ℝ) m]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith only [hpm]) (jetNorm_nonneg _ _ _ _)) (jetNorm_nonneg _ _ _ _)

theorem jet_tame_product (e : ι → E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (m j : ℕ)
    (hm : 0 < m) (hj : j ≤ m) :
    jetNorm e f j (exponent m j)*jetNorm e f (m-j) (exponent m (m-j)) ≤
    (2*(m:ℝ))^(j*(m-j))*jetNorm e f 0 ∞*jetNorm e f m 2 := by
  have h := nonnegative_sequence_product m j hm hj
    (fun i => jetNorm e f i (exponent m i)) (fun _ => jetNorm_nonneg _ _ _ _)
    (2*(m:ℝ)) (by
      have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      linarith only [this])
    (fun i hi => jet_exponent_recurrence e hf hc m hm i hi)
  have he : exponent m m = 2 := by
    rw [exponent_of_pos hm hm]
    have hmn : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    rw [mul_div_cancel_right₀ _ hmn]
    norm_num
  simpa only [exponent_zero,he] using h
end TameInterpolation

end
end

end OAI
