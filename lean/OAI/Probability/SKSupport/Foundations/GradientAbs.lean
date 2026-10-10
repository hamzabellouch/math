import Mathlib
import OAI.Probability.SKSupport.Control.ExpectedControlPayoff

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

lemma gradient_abs_le_one (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) : |gradient W γ t x| ≤ 1 := by
  simpa only [gradient, Real.norm_eq_abs, NNReal.coe_one] using
    (norm_deriv_le_of_lipschitz (x₀ := x) (value_lipschitz W γ t ht))

lemma integral_weighted_difference_bound {g h a : ℝ → ℝ} (hg : Integrable g)
    (hh : Integrable h) (ha : Measurable a) (hbound : ∀ s, |a s| ≤ 1)
    (t : ℝ) (ht : t ≤ 1) :
    |(∫ s in t..1, g s*a s) - (∫ s in t..1, h s*a s)| ≤
      ∫ s in t..1, |g s-h s| := by
  have hg' : Integrable (fun s => g s*a s) := hg.mul_bdd ha.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s => by simpa only [Real.norm_eq_abs] using hbound s))
  have hh' : Integrable (fun s => h s*a s) := hh.mul_bdd ha.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s => by simpa only [Real.norm_eq_abs] using hbound s))
  rw [← intervalIntegral.integral_sub hg'.intervalIntegrable hh'.intervalIntegrable,
    ← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le ht _ (hg.sub hh).abs.intervalIntegrable
  exact Filter.Eventually.of_forall (fun s _ => by
    simp only [Pi.sub_apply, Real.norm_eq_abs, ← sub_mul, abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hbound s) (abs_nonneg (g s-h s)))

lemma controlPayoff_coeff_le (W : BrownianSystem Ω) (γ η : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    controlPayoff W γ t x α ω ≤ controlPayoff W η t x α ω +
      (3 / 2 : ℝ) * ∫ s in t..1, |extend γ.val s-extend η.val s| := by
  have ha : Measurable (fun s : ℝ => α.val (Real.toNNReal (s-t)) ω) :=
    (α.measurable_elapsed t).comp measurable_prodMk_right
  have hd := integral_weighted_difference_bound γ.integrable η.integrable ha
    (fun s => α.bound _ _) t ht
  have hc := integral_weighted_difference_bound γ.integrable η.integrable (ha.pow_const 2)
    (fun s => by simpa only [abs_pow, one_pow, Function.comp_apply] using
      pow_le_pow_left₀ (abs_nonneg _) (α.bound (Real.toNNReal (s-t)) ω) 2) t ht
  have htri := abs_add_le
    (x + W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend η.val s * α.val (Real.toNNReal (s-t)) ω)
    ((∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s-t)) ω) -
      ∫ s in t..1, extend η.val s * α.val (Real.toNNReal (s-t)) ω)
  have heq : x + W.B 1 ω - W.B (Real.toNNReal t) ω +
      (∫ s in t..1, extend η.val s * α.val (Real.toNNReal (s-t)) ω) +
      ((∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s-t)) ω) -
      ∫ s in t..1, extend η.val s * α.val (Real.toNNReal (s-t)) ω) =
      x + W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s-t)) ω := by ring
  rw [heq] at htri
  have hcost := neg_le_abs
    ((∫ s in t..1, extend γ.val s * (α.val (Real.toNNReal (s-t)) ω)^2) -
      ∫ s in t..1, extend η.val s * (α.val (Real.toNNReal (s-t)) ω)^2)
  dsimp [controlPayoff]
  linarith

lemma value_coeff_le (W : BrownianSystem Ω) (γ η : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) : value W γ t x ≤ value W η t x +
      (3 / 2 : ℝ) * ∫ s in t..1, |extend γ.val s-extend η.val s| := by
  let := W.isProbability
  unfold value
  refine csSup_le ?_ ?_
  · exact ⟨_, ⟨zeroControl W (Real.toNNReal t), rfl⟩⟩
  rintro _ ⟨α, rfl⟩
  calc
    (∫ ω, controlPayoff W γ t x α ω ∂W.law) ≤
        ∫ ω, (controlPayoff W η t x α ω +
          (3 / 2 : ℝ) * ∫ s in t..1, |extend γ.val s-extend η.val s|) ∂W.law :=
      integral_mono (controlPayoff_integrable W γ t x ht α)
        ((controlPayoff_integrable W η t x ht α).add (integrable_const _))
        (controlPayoff_coeff_le W γ η t x ht α)
    _ = (∫ ω, controlPayoff W η t x α ω ∂W.law) +
        (3 / 2 : ℝ) * ∫ s in t..1, |extend γ.val s-extend η.val s| := by
      rw [integral_add (controlPayoff_integrable W η t x ht α) (integrable_const _)]
      simp
    _ ≤ _ := add_le_add (expected_controlPayoff_le_value W η t x ht α) le_rfl

theorem value_coefficient_stability (W : BrownianSystem Ω) (γ η : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) : |value W γ t x - value W η t x| ≤
      (3 / 2 : ℝ) * ∫ s in t..1, |extend γ.val s-extend η.val s| := by
  rw [abs_le]
  have h₁ := value_coeff_le W γ η t x ht
  have h₂ := value_coeff_le W η γ t x ht
  simp_rw [abs_sub_comm (extend η.val _) (extend γ.val _)] at h₂
  constructor <;> linarith

end ZeroTemperatureSK

end
end

end OAI
