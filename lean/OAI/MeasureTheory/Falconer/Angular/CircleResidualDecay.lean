import OAI.MeasureTheory.Falconer.Angular.CompactCircleResidual
import OAI.MeasureTheory.Falconer.Geometry.CompactMultiplierScale
import OAI.MeasureTheory.Falconer.Angular.AngularNonstationary

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem circle_residual_uniform_decay (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    ∀ {C D Λ : ℝ}, 0 ≤ C → 1 ≤ D → 0 < Λ →
    (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖∫ x : ℝ, cosineOscillator Λ x * circleResidualAmplitude f x‖ ≤ A*C*D^n/Λ^n := by
  let w : ℝ → ℂ := fun x => (compactCircleResidual x : ℂ)
  have hw : ContDiff ℝ ∞ w := Complex.ofRealCLM.contDiff.comp compactCircleResidual_contDiff
  have hws : tsupport w ⊆ Icc (-Real.pi) Real.pi := by
    apply Subset.trans _ compactCircleResidual_tsupport
    apply closure_mono
    intro x hx hh
    exact hx (by simp [w,hh])
  obtain ⟨B,hB,hprod⟩ := compact_multiplier_uniform_derivatives hw isCompact_Icc hws n
  obtain ⟨A,hA,hbound⟩ := angular_nonstationary_uniform (by norm_num : (0:ℝ)<1/8)
    (neg_le_self Real.pi_pos.le) n
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro f hf C D Λ hC hD hΛ hb
  have hs : tsupport (circleResidualAmplitude f) ⊆ Icc (-Real.pi) Real.pi :=
    (circleResidualAmplitude_support f).trans compactCircleResidual_tsupport
  have haway : ∀ x ∈ tsupport (circleResidualAmplitude f), (1:ℝ)/8 ≤ |Real.sin x| :=
    fun x hx => compactCircleResidual_sine_support (circleResidualAmplitude_support f hx)
  have hder : ∀ k ≤ n, ∀ x, ‖iteratedDeriv k (circleResidualAmplitude f) x‖ ≤ (B*C)*D^k :=
    hprod hf hC hD hb
  have hh := hbound (circleResidualAmplitude_contDiff hf) hs haway (mul_nonneg hB hC) hD hΛ hder
  convert hh using 1
  ring

end PlanarFalconer

end OAI
