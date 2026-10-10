import OAI.Probability.MatroidSecretary.Secretary.ReplayRule
import OAI.Probability.MatroidSecretary.Transport.AdversarialMinimum

namespace OAI

/-!
# Integrating the actual reconstructed secretary rule

This is a supporting composition theorem. The correct source marginal and
mask-support facts are explicit inputs to be supplied by the concrete finite
prefix/table coupling; they are not premises of the final secretary endpoint.
The adversarial order may depend on all of the ambient randomness, including
unused precommitted table entries.
-/

namespace MatroidProphet.SecretaryReplay

open MeasureTheory

/-- Replay and the expected-minimum comparison commute with an arbitrary
measurable full-information suffix policy. Prefix-set equality follows, in the
secretary experiment, from agreement with the sampled ordered prefix. -/
theorem reconstructed_integral_lower {n bits : ℕ} {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (A : HiddenRule n bits) (K : Q → Fin (n + 1))
    (decode : Q → Finset (Fin n) → Seed bits) (w : Weights n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : Measure (Seed bits)) (q : Ω → Q) (σ π : Ω → ArrivalOrder n)
    (hq : Measurable q) (hσ : Measurable σ) (hπ : Measurable π)
    (hprefix : ∀ᵐ ω ∂μ,
      orderPrefix (π ω) (K (q ω)).val = orderPrefix (σ ω) (K (q ω)).val)
    (hmask : ∀ᵐ ω ∂μ,
      A.mask (decode (q ω) (orderPrefix (σ ω) (K (q ω)).val)) =
        orderPrefix (σ ω) (K (q ω)).val)
    (hlaw : μ.map (fun ω => decode (q ω) (orderPrefix (σ ω) (K (q ω)).val)) = ν) :
    Integrable (fun ω => secretaryReward (reconstructedRule A K decode) (q ω) w (π ω)) μ ∧
      (∫ r, hiddenWorstReward A w r ∂ν) ≤
        ∫ ω, secretaryReward (reconstructedRule A K decode) (q ω) w (π ω) ∂μ := by
  have hR : Measurable
      (fun ω => decode (q ω) (orderPrefix (σ ω) (K (q ω)).val)) :=
    (measurable_of_finite (fun z : Q × ArrivalOrder n =>
      decode z.1 (orderPrefix z.2 (K z.1).val))).comp (hq.prodMk hσ)
  refine hiddenWorstReward_integral_le_replayed A w μ ν
    (fun ω => decode (q ω) (orderPrefix (σ ω) (K (q ω)).val)) π hR hπ hlaw
    (fun ω => secretaryReward (reconstructedRule A K decode) (q ω) w (π ω)) ?_
  filter_upwards [hprefix, hmask] with ω hp hm
  have hm' : A.mask (decode (q ω) (orderPrefix (π ω) (K (q ω)).val)) =
      orderPrefix (π ω) (K (q ω)).val := by
    rw [hp]
    exact hm
  rw [reconstructed_reward A K decode (q ω) w (π ω) hm', hp]

end MatroidProphet.SecretaryReplay

end OAI
