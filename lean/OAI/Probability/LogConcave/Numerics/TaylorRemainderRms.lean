import Mathlib
import OAI.Probability.LogConcave.Numerics.ChainTaylor

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set

variable {β E : Type*} [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ν : Measure β} [SFinite ν]

theorem taylor_remainder_rms {f : ℝ → β → E} {n : ℕ} {a x B : ℝ}
    (hax : a≤x) (hB0 : 0≤B) (hf : ∀z,ContDiff ℝ (n+1:ℕ) (fun t => f t z))
    (hm : AEStronglyMeasurable (fun p : ℝ × β => iteratedDeriv (n+1) (fun t => f t p.2) p.1)
      ((volume.restrict (Ioc a x)).prod ν))
    (hi : ∀t∈Ioc a x,Integrable (fun z => ‖iteratedDeriv (n+1) (fun s => f s z) t‖^2) ν)
    (hB : ∀t∈Ioc a x,(∫z,‖iteratedDeriv (n+1) (fun s => f s z) t‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖f x z-taylorWithinEval (fun t => f t z) n univ a x‖^2) ν ∧
      (∫z,‖f x z-taylorWithinEval (fun t => f t z) n univ a x‖^2 ∂ν)≤
        ((x-a)^(n+1)/(n.factorial:ℝ))^2*B := by
  let μ : Measure ℝ := volume.restrict (Ioc a x)
  let w : ℝ → ℝ := fun t => (x-t)^n/(n.factorial:ℝ)
  have hw : AEStronglyMeasurable w μ := by
    apply Continuous.aestronglyMeasurable
    dsimp [w]; fun_prop
  have hk : ∀ᵐ t ∂μ,|w t|≤(x-a)^n/(n.factorial:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact taylor_kernel_bound ht.1.le ht.2 n
  have hs : ∀ᵐ t ∂μ,Integrable (fun z => ‖iteratedDeriv (n+1) (fun s => f s z) t‖^2) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hi t ht
  have hb : ∀ᵐ t ∂μ,(∫z,‖iteratedDeriv (n+1) (fun s => f s z) t‖^2 ∂ν)≤B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB t ht
  have hv := RMSIntegral.weighted_time_seed hm hw hB0 hk hs hb
  have he (z : β) : f x z-taylorWithinEval (fun t => f t z) n univ a x=
      ∫t,w t • iteratedDeriv (n+1) (fun s => f s z) t ∂μ := by
    rw [taylor_remainder_global (hf z),intervalIntegral.integral_of_le hax]
  have hμ : μ.real univ=x-a := by
    dsimp only [μ,Measure.real]
    rw [Measure.restrict_apply_univ]
    exact Real.volume_real_Ioc_of_le hax
  simp_rw [he]
  refine ⟨hv.1,hv.2.trans_eq ?_⟩
  rw [hμ, pow_succ (x-a) n]
  ring
end LogConcaveSampling.Quadrature

end

end

end

end OAI
