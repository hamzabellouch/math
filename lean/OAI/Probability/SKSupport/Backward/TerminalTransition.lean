import Mathlib
import OAI.Probability.SKSupport.Backward.TerminalTailValue
import OAI.Probability.SKSupport.Moments.StripSquareMoment

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma value_regular (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : RegularDatum (value W γ t) := by
  refine ⟨value_contDiff W γ ht0 ht1,?_⟩
  have hh := (compactGradient_family W γ ht0 ht1).regular t
  change BoundedSmooth (deriv (value W γ (stripClamp t t))) at hh
  rw [stripClamp_eq (show t ∈ Icc (0:ℝ) t from ⟨ht0,le_rfl⟩)] at hh
  exact hh

lemma gradientDefect_smooth (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : BoundedSmooth (fun x => 1-(gradient W γ t x)^2) := by
  have hu := (value_regular W γ ht0 ht1).deriv_bounded
  convert (BoundedSmooth.const 1).add ((hu.mul hu).const_mul (-1)) using 1
  funext x
  unfold gradient
  ring

theorem terminal_plateau_transition (W : BrownianSystem Ω) (γ : OrderParameter)
    {a c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ r ∈ Ioo a 1, extend γ.val r=c)
    (s T : Time) (has : a < (s:ℝ)) (hsT : s ≤ T) {g : ℝ → ℝ} (hg : BoundedSmooth g) :
    (∫ ξ, g (diffusion W γ (⟨T,T.property.1⟩:ℝ≥0) ξ) ∂W.law)=
      ∫ ξ, varianceTilted c ((T:ℝ)-s) (value W γ T) g
        (diffusion W γ (⟨s,s.property.1⟩:ℝ≥0) ξ) ∂W.law := by
  have hm : ∀ t ∈ Ico (s:ℝ) T, ∀ x,
      (stripDrift W γ T).f t x=c*deriv (varianceLogHeat c ((T:ℝ)-t) (value W γ T)) x := by
    intro t ht x
    rw [stripDrift_eq W γ T ⟨s.property.1.trans ht.1,ht.2.le⟩,
      hc t ⟨has.trans_le ht.1,ht.2.trans T.property.2⟩]
    unfold gradient
    rw [value_plateau_semigroup W γ hc0 (s.property.1.trans ht.1) (has.trans_le ht.1) ht.2.le T.property.2 hc]
  have hh := expected_transition_tiltedMean W (stripDrift W γ T)
    (value_regular W γ T.property.1 T.property.2) (value_lipschitz W γ T T.property.2.le) hg hc0
    (a := (⟨s,s.property.1⟩:ℝ≥0)) (T := (⟨T,T.property.1⟩:ℝ≥0)) hsT hm
  have eT : diffusion W γ (⟨T,T.property.1⟩:ℝ≥0)=(stripDrift W γ T).solution W.driver (⟨T,T.property.1⟩:ℝ≥0) :=
    funext (diffusion_eq_strip W γ T (⟨T,T.property.1⟩:ℝ≥0) le_rfl)
  have es : diffusion W γ (⟨s,s.property.1⟩:ℝ≥0)=(stripDrift W γ T).solution W.driver (⟨s,s.property.1⟩:ℝ≥0) :=
    funext (diffusion_eq_strip W γ T (⟨s,s.property.1⟩:ℝ≥0) hsT)
  rw [eT,es]
  exact hh

end ZeroTemperatureSK

end
end

end OAI
