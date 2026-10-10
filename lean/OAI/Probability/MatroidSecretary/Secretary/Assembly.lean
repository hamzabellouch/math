import OAI.Probability.MatroidSecretary.Secretary.LawTransfer
import OAI.Probability.MatroidSecretary.Secretary.ReplayTransport

namespace OAI

open MeasureTheory ProbabilityTheory

namespace MatroidProphet.SecretaryReplay

lemma prefix_set_eq {n : ℕ} {K : ℕ} {σ π : ArrivalOrder n}
    (h : SamePrefix K σ π) : orderPrefix σ K = orderPrefix π K := by
  ext e
  simp only [mem_orderPrefix]
  constructor
  · intro he
    have hp := h (σ.symm e) he
    have heq : π.symm e = σ.symm e := by
      apply π.injective
      simpa using hp
    simpa [heq] using he
  · intro he
    have hp := h (π.symm e) he
    have heq : σ.symm e = π.symm e := by
      apply σ.injective
      simpa using hp.symm
    simpa [heq] using he

/-- A finite product coupling supplies the entire arbitrary-ambient-space lower
bound. In particular nothing here requires independence of the executed order. -/
theorem reconstructed_product_lower {n bits : ℕ} {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (A : HiddenRule n bits) (K : Q → Fin (n + 1))
    (decode : Q → Finset (Fin n) → Seed bits)
    (νQ : Measure Q) (η : Measure (ArrivalOrder n)) (ν : Measure (Seed bits))
    (hproductLaw : (νQ.prod η).map
      (fun z => decode z.1 (orderPrefix z.2 (K z.1).val)) = ν)
    (hproductMask : ∀ᵐ z ∂νQ.prod η,
      A.mask (decode z.1 (orderPrefix z.2 (K z.1).val)) =
        orderPrefix z.2 (K z.1).val)
    (w : Weights n) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → Q) (σ π : Ω → ArrivalOrder n)
    (hq : Measurable q) (hσ : Measurable σ) (hπ : Measurable π)
    (hqlaw : μ.map q = νQ) (hσlaw : μ.map σ = η)
    (hind : IndepFun q σ μ)
    (hprefix : ∀ᵐ ω ∂μ, SamePrefix (K (q ω)).val (σ ω) (π ω)) :
    Integrable (fun ω => secretaryReward (reconstructedRule A K decode) (q ω) w (π ω)) μ ∧
      (∫ r, hiddenWorstReward A w r ∂ν) ≤
        ∫ ω, secretaryReward (reconstructedRule A K decode) (q ω) w (π ω) ∂μ := by
  have hlaw := secretary_reconstruction_law μ νQ η ν
    (fun z => decode z.1 (orderPrefix z.2 (K z.1).val))
    (measurable_of_finite _) hproductLaw q σ hq hσ hqlaw hσlaw hind
  have hmask := secretary_product_ae μ νQ η q σ hq hσ hqlaw hσlaw hind
    (fun z => A.mask (decode z.1 (orderPrefix z.2 (K z.1).val)) =
      orderPrefix z.2 (K z.1).val) hproductMask
  apply reconstructed_integral_lower A K decode w μ ν q σ π hq hσ hπ
    _ hmask hlaw.map_eq
  filter_upwards [hprefix] with ω hω
  exact (prefix_set_eq hω).symm

end MatroidProphet.SecretaryReplay

end OAI
