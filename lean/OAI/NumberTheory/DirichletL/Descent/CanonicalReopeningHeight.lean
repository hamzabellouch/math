import OAI.NumberTheory.DirichletL.Descent.DescentHeight
import OAI.NumberTheory.DirichletL.Descent.CanonicalLongSource

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff

namespace SevenEighths.InverseMoment
open MeasureTheory CanonicalCubeSeparation FourierBridge JointLogSeparation CompletedHeight

theorem reopening_coefficient_twist (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(theta:ℝ)
    (hT:ContDiff ℝ ∞ (normTwistedSource W theta)):
    reopeningCoefficient (normTwistedSource W theta) a b ha
      ((normTwistedSource_support W theta).trans hs) hT=
      𝓕 (frequencyTwist (sourceLogProfile W a b ha hs hW) theta) :=by
  unfold reopeningCoefficient
  congr 1
  ext x
  simp only [sourceLogProfile_apply,frequencyTwist_apply,normTwistedSource,Real.log_exp]

theorem reopening_twisted_moment (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(J:ℕ):
    ∃C:ℝ,0≤C ∧ ∀theta:ℝ,∀hT:ContDiff ℝ ∞ (normTwistedSource W theta),
      (∫ξ:ℝ,‖reopeningCoefficient (normTwistedSource W theta) a b ha
        ((normTwistedSource_support W theta).trans hs) hT ξ‖*(1+|ξ|)^J)≤
      C*(1+‖theta‖)^(J+(volume:Measure ℝ).integrablePower) :=by
  obtain ⟨C,hC,he⟩:=frequencyTwist_fourier_moment J (sourceLogProfile W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro theta hT
  rw [reopening_coefficient_twist W a b ha hs hW theta hT]
  simpa only [Real.norm_eq_abs,mul_comm] using he theta

theorem reopening_twisted_moment_squared (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(J:ℕ):
    ∃C:ℝ,0≤C ∧ ∀theta:ℝ,∀hT:ContDiff ℝ ∞ (normTwistedSource W theta),
      (∫ξ:ℝ,‖reopeningCoefficient (normTwistedSource W theta) a b ha
        ((normTwistedSource_support W theta).trans hs) hT ξ‖*(1+|ξ|)^J)^2≤
      C*(1+‖theta‖)^(2*(J+(volume:Measure ℝ).integrablePower)) :=by
  obtain ⟨C,hC,he⟩:=reopening_twisted_moment W a b ha hs hW J
  refine ⟨C^2,sq_nonneg _,?_⟩
  intro theta hT
  have hh:=pow_le_pow_left₀ (integral_nonneg (fun ξ=>by positivity)) (he theta hT) 2
  simpa only [mul_pow,←pow_mul,Nat.mul_comm] using hh

end SevenEighths.InverseMoment

end

end OAI
