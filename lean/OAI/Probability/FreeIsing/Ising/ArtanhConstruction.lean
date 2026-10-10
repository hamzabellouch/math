import OAI.Probability.FreeIsing.Ising.ContinuousPosterior
import OAI.Probability.FreeIsing.Ising.LocalizedArtanh

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367

theorem HasFreeIsingLaw.exists_jointExit_artanh
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ omega, Continuous (fun t => B t omega)) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let F := ArrayPosteriorStationarity.filtration B hmB
    ∃ m : TreeVertex d → ℝ≥0 → IsingInnovation.State d Ω → ℝ,
      (∀ v, IsStronglyPredictable F (m v)) ∧
      (∀ v, ∀ᵐ p ∂P, Continuous (fun t => m v t p)) ∧
      (∀ v t, m v t =ᵐ[P] IsingInnovation.posterior beta B v t) ∧
      ∀ v, IsingJointExitArtanhData beta (fun _ => B) (fun _ => hmB) m v P := by
  choose m hp hm hc h2 hz hv using
    (fun v : TreeVertex d => IsingInnovation.exists_continuous_posterior
      hd hμ hb hcrit ν hB hmB hcB v)
  refine ⟨m, hp, hc, hv, fun v => ?_⟩
  have hBrownian : IsBrownianReal B ν := ⟨hB, Filter.Eventually.of_forall hcB⟩
  have hg (w : TreeVertex d) : IsStronglyProgressive
      (arrayObservationFiltration (fun _ : TreeVertex d => B) (fun _ => hmB)
        FiniteIsingFiltering.signal FiniteIsingFiltering.measurable_signal) (m w) :=
    (hp w).isStronglyProgressive
  have hv' (w : TreeVertex d) (t : ℝ≥0) :
      m w t =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
        (fun p => infiniteGibbsSpinMean beta w
          (fun i => (t : ℝ) * spinSign (p.1 i) + B t (p.2 i))) := by
    apply (hv w t).trans
    apply Filter.Eventually.of_forall
    intro p
    apply congrArg (infiniteGibbsSpinMean beta w)
    funext i
    exact add_comm _ _
  exact hμ.continuous_posterior_jointExit_artanh hd hb hcrit (fun _ => ν)
    (fun _ => hBrownian) (fun _ => hmB) (fun _ => hcB) hg hc hv' v

end Problem367

end

end OAI
