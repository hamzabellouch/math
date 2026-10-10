import OAI.Probability.InvariantIsing.Magnetic.RestrictedTreeLogMeasurability
import OAI.Probability.InvariantIsing.Magnetic.RestrictedCanonicalLogIntegrability

namespace OAI

/-! The canonical capped logarithm remains integrable after averaging
an arbitrary finite cascade law and the independent compression data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma integrable_restricted_canonical_tree_log {Ω : Type*} [MeasurableSpace Ω]
    {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (t cap δ : ℝ) (hcap : 0 ≤ cap)
    (A : Ω → CavityFactorBlocks d n) (hA : Measurable A) {D : ℝ}
    (hAb : ∀ ω, cavityFactorSize (A ω).1 (A ω).2.1 (A ω).2.2 ≤ D) :
    Integrable (fun z : LabeledTree depth × (Ω × Orthogonal N) =>
      restrictedProjectorCappedLog S hS C hC z.1 (fun a => t*lam a+2*perturbationScale N*v a)
        u t cap δ (A z.2.1)
        (cavityLabeledProjectorAction z.2.2 (cavityCanonicalProjectorFrame k e a₀)))
      (θ.prod (P.prod ν)) := by
  have hp : Measurable (fun z : LabeledTree depth × (Ω × Orthogonal N) =>
      cavityLabeledProjectorAction z.2.2 (cavityCanonicalProjectorFrame k e a₀)) :=
    (measurable_cavityCanonicalProjectorAction k e a₀).comp measurable_snd.snd
  have hm := measurable_restrictedProjectorCappedLog_tree S hS C hC Prod.fst measurable_fst
    (fun a => t*lam a+2*perturbationScale N*v a) u t cap δ
    (fun z : LabeledTree depth × (Ω × Orthogonal N) => A z.2.1)
    (hA.comp measurable_snd.fst) _ hp
  apply Integrable.of_bound hm.aestronglyMeasurable ((|t| *D+|δ|)*(1+N))
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs]
    exact restricted_canonical_capped_log_bound S hS C hC k e a₀ z.2.2 z.1 lam v u hu
      t cap δ hcap (A z.2.1) (hAb z.2.1)

end InvariantIsing

end

end OAI
