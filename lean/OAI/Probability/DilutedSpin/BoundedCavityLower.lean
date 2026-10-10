import OAI.Probability.DilutedSpin.IncrementErrorLimit
import OAI.Probability.DilutedSpin.UpperTrial

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter Set ConcreteReservoir
open scoped NNReal Topology

lemma bounded_symmetric_trial_lower {q : ℕ} (M : Model (q+1)) (hα : 0 < M.alpha)
    {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure,|h|≤H)
    (hθi : Integrable (fun z : InteractionSample (q+1) => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun z : InteractionSample (q+1) => z.1)
      (fun z : InteractionSample (q+1) => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ),Exponents m ∧
      functional M r ζ m ≤ liminf (pressure M) atTop+ε := by
  have hθ' : ∀ᵐ z ∂M.disorder.toMeasure,∀ σ,|z.1 σ|≤C := hθ.mono (fun z hz σ =>
    (show |z.1 σ|≤‖z.1‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z.1 σ).trans hz)
  obtain ⟨Ns,us,hNs,hu,hinc,hcontrol,_⟩ := full_regular_covariance_selection M hC hH hθ' hh hθi hhi
    (show 0 < ε/4 by positivity)
  let gap := fun L n => |cavityProxy M C H (Ns L n+1) L (us L n)-
    functional M L (reservoirTrialLaw M C H (Ns L n+1) L (us L n)) (fun i => gridExponents L i.castSucc)|
  have hlim : Tendsto (fun L => limsup (gap L) atTop) atTop (𝓝 0) :=
    cavityProxy_comparison_tendsto M hα hC hH hθ hh hθi hhi Ns (fun L => (hNs L).tendsto_atTop) us hcontrol
  have hL := ((tendsto_order.1 hlim).2 (ε/4) (by positivity)).exists
  obtain ⟨L,hL⟩ := hL
  have hB : IsBoundedUnder (·≤·) atTop (gap L) := isBoundedUnder_of_eventually_le
    (Eventually.of_forall (fun n => cavityProxy_functional_bound M hθ hh hθi hhi (Ns L n+1) L (us L n)))
  have hsmall : ∀ᶠ n in atTop,gap L n<ε/4 := eventually_lt_of_limsup_lt hL hB
  have hNlim : Tendsto (fun n => Ns L n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp (hNs L).tendsto_atTop
  have herr := (cavityIncrementError_tendsto M.alpha q C).comp hNlim
  have hevent : ∀ᶠ n in atTop,cavityIncrementError M.alpha q C (Ns L n+1)<ε/4 :=
    (tendsto_order.1 herr).2 (ε/4) (by positivity)
  obtain ⟨n,hn,he⟩ := (hsmall.and hevent).exists
  refine ⟨L,reservoirTrialLaw M C H (Ns L n+1) L (us L n),
    (fun i => gridExponents L i.castSucc),gridExponents_exponents L,?_⟩
  have hp := increment_cavityProxy_bound M hC hH hθ' hh hsym (Ns L n) (us L n)
  have hg := (abs_lt.mp hn).1
  have hi := (abs_le.mp hp).1
  have hb := hinc L n
  linarith
end DilutedSpinGlass.UniversalDictionary

end

end OAI
