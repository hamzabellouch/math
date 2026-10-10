import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCutoff

namespace OAI

/-! Measurability of a normalized cutoff when the labeled cascade prior
is part of the retained disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma measurable_random_cavityCutoffReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H) (s : Ω → Set X)
    (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    (F : Ω × (Fin 2 → X) → ℝ) (hF : Measurable F) :
    Measurable (fun ω => cavityCutoffReplicaMean (ν ω) (fun x => H (ω,x)) (s ω)
      (fun σ => F (ω,σ))) := by
  classical
  have hS : MeasurableSet {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} := by
    have he : {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} =
        ⋂ i, {p : Ω × (Fin 2 → X) | p.2 i ∈ s p.1} := by ext p; simp
    rw [he]
    exact MeasurableSet.iInter (fun i => hs.preimage
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hn := measurable_random_referenceReplicaMean hν hH
    (D := fun p : Ω × (Fin 2 → X) => if ∀ i, p.2 i ∈ s p.1 then F p else (0 : ℝ))
    (Measurable.ite hS hF measurable_const)
  have hd := measurable_random_referenceReplicaMean hν hH
    (D := fun p : Ω × (Fin 2 → X) => if ∀ i, p.2 i ∈ s p.1 then (1 : ℝ) else 0)
    (Measurable.ite hS measurable_const measurable_const)
  exact hn.div hd

end InvariantIsing

end

end OAI
