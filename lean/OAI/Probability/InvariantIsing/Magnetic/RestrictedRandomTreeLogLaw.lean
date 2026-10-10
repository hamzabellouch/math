import OAI.Probability.InvariantIsing.Magnetic.RestrictedRandomHaarLog
import OAI.Probability.InvariantIsing.Magnetic.RestrictedCanonicalTreeLogLaw
import OAI.Probability.InvariantIsing.Magnetic.RestrictedTreeLogIntegrability
import OAI.Probability.InvariantIsing.Cavity.CavityExtraLogAverage

namespace OAI

/-! The random-compression version of the canonical logarithmic law.
The compression variable is independent of the base disorder and the
fresh spectral-group rotations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem restricted_random_tree_log_law {Z : Type*} [MeasurableSpace Z] {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (P : Measure Z) [IsProbabilityMeasure P]
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))
    [IsProbabilityMeasure η]
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (t cap δ : ℝ) (hcap : 0 ≤ cap)
    (A : Z → CavityFactorBlocks d n) (hA : Measurable A) {D : ℝ}
    (hAb : ∀ z, cavityFactorSize (A z).1 (A z).2.1 (A z).2.2 ≤ D) :
    (∫ T, ∫ z, restrictedProjectorCappedLog S hS C hC T
      (fun a => t*lam a+2*perturbationScale N*v a) u t cap δ (A z.1)
      (cavityLabeledProjectorAction z.2 (cavityCanonicalProjectorFrame k e a₀)) ∂P.prod μ ∂θ) =
    ∫ p, restrictedRandomHaarLog S hS C hC k e a₀ hk lam v u t cap δ A p
      ∂(P.prod ((μ.prod θ).prod gaussianCoordinates)).prod η := by
  let f : LabeledTree depth × (Z × Orthogonal N) → ℝ := fun z : LabeledTree depth × (Z × Orthogonal N) =>
    restrictedProjectorCappedLog S hS C hC z.1 (fun a => t*lam a+2*perturbationScale N*v a)
      u t cap δ (A z.2.1)
      (cavityLabeledProjectorAction z.2.2 (cavityCanonicalProjectorFrame k e a₀))
  have hp : Measurable (fun z : LabeledTree depth × (Z × Orthogonal N) =>
      cavityLabeledProjectorAction z.2.2 (cavityCanonicalProjectorFrame k e a₀)) :=
    (measurable_cavityCanonicalProjectorAction k e a₀).comp measurable_snd.snd
  have hf : Measurable f := measurable_restrictedProjectorCappedLog_tree S hS C hC Prod.fst measurable_fst
    (fun a => t*lam a+2*perturbationScale N*v a) u t cap δ
    (fun z : LabeledTree depth × (Z × Orthogonal N) => A z.2.1)
    (hA.comp measurable_snd.fst) _ hp
  have hb z : |f z| ≤ (|t| *D+|δ|)*(1+N) :=
    restricted_canonical_capped_log_bound S hS C hC k e a₀ z.2.2 z.1 lam v u hu t cap δ hcap
      (A z.2.1) (hAb z.2.1)
  have hcycle := cavity_bounded_three_integral_cycle θ P μ f hf hb
  let F : (Z × ((Orthogonal N × LabeledTree depth) × (ℕ → ℝ))) ×
      ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)) → ℝ := restrictedRandomHaarLog (depth := depth) S hS C hC k e a₀ hk lam v u t cap δ A
  have hF : Measurable F := measurable_restrictedRandomHaarLog S hS C hC k e a₀ hk lam v u t cap δ A hA
  have hFb p : |F p| ≤ (|t| *D+|δ|)*(1+N) :=
    restrictedRandomHaarLog_bound S hS C hC k e a₀ hk lam v u t cap δ hcap A hAb p
  have he := cavity_bounded_extra_product_integral P ((μ.prod θ).prod gaussianCoordinates)
    η F hF hFb
  calc
    _ = ∫ z, ∫ T, ∫ V, f (T,(z,V)) ∂μ ∂θ ∂P := hcycle
    _ = ∫ z, ∫ p, F ((z,p.1),p.2)
        ∂(((μ.prod θ).prod gaussianCoordinates).prod η) ∂P := by
      apply integral_congr_ae
      apply ae_of_all
      intro z
      exact restricted_canonical_tree_log_law S hS C hC k e a₀ hk μ η θ lam v u hu t cap δ hcap (A z)
    _ = _ := he.symm

end InvariantIsing

end

end OAI
