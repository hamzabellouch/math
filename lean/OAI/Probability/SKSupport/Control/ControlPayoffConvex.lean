import Mathlib
import OAI.Probability.SKSupport.Control.ExpectedControlPayoff

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

lemma controlPayoff_convex (W : BrownianSystem Ω) (γ : OrderParameter)
    (t : ℝ) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    ConvexOn ℝ Set.univ (fun x => controlPayoff W γ t x α ω) := by
  have h := ((convexOn_norm (E := ℝ) (s := Set.univ) convex_univ).translate_left
    (W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s-t)) ω)).add_const
    (-(1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s * (α.val (Real.toNNReal (s-t)) ω)^2)
  simpa only [Set.preimage_univ, Function.comp_def, Pi.add_def, Pi.add_apply, Real.norm_eq_abs, controlPayoff,
    sub_eq_add_neg, neg_mul, add_assoc] using h

lemma expected_controlPayoff_convex (W : BrownianSystem Ω) (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    ConvexOn ℝ Set.univ (fun x => ∫ ω, controlPayoff W γ t x α ω ∂W.law) := by
  exact integral_convexOn_of_integrand_ae convex_univ
    (Filter.Eventually.of_forall (controlPayoff_convex W γ t α))
    (fun x _ => controlPayoff_integrable W γ t x ht α)

theorem value_convex (W : BrownianSystem Ω) (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) : ConvexOn ℝ Set.univ (value W γ t) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  change sSup (Set.range (fun α : Control W (Real.toNNReal t) =>
    ∫ ω, controlPayoff W γ t (a*x+b*y) α ω ∂W.law)) ≤ _
  refine csSup_le ?_ ?_
  · exact ⟨_, ⟨zeroControl W (Real.toNNReal t), rfl⟩⟩
  rintro _ ⟨α, rfl⟩
  calc
    _ ≤ a * (∫ ω, controlPayoff W γ t x α ω ∂W.law) +
        b * (∫ ω, controlPayoff W γ t y α ω ∂W.law) := by
      simpa only [smul_eq_mul] using
        (expected_controlPayoff_convex W γ t ht α).2 hx hy ha hb hab
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (expected_controlPayoff_le_value W γ t x ht α) ha)
      (mul_le_mul_of_nonneg_left (expected_controlPayoff_le_value W γ t y ht α) hb)

lemma OrderParameter.local_bound (γ : OrderParameter) (t b : Time) (htb : t ≤ b) :
    γ.val t ≤ (∫ s in (0 : ℝ)..1, extend γ.val s) / (1 - (b : ℝ)) := by
  have hpoint : (fun _ : ℝ => γ.val t) ≤ᵐ[volume.restrict (Set.Icc (b : ℝ) 1)] extend γ.val := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [volume.ae_ne (1 : ℝ)] with s hs hsb
    have hs1 : s < 1 := lt_of_le_of_ne hsb.2 hs
    have hs0 : 0 ≤ s := le_trans b.property.1 hsb.1
    have hts : t ≤ (⟨s, hs0, hs1⟩ : Time) := le_trans htb hsb.1
    simpa only [extend, dite_eq_left (show s ∈ Set.Ico (0 : ℝ) 1 from ⟨hs0, hs1⟩)] using
      γ.monotone hts
  have hlow := intervalIntegral.integral_mono_ae_restrict b.property.2.le
    (intervalIntegrable_const (c := γ.val t)) γ.integrable.intervalIntegrable hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hlow
  have hupper := intervalIntegral.integral_mono_interval b.property.1 b.property.2.le
    (le_refl (1 : ℝ)) (Filter.Eventually.of_forall (fun s => γ.extend_nonneg s))
    γ.integrable.intervalIntegrable
  apply (le_div_iff₀ (sub_pos.mpr b.property.2)).2
  linarith

end ZeroTemperatureSK

end
end

end OAI
