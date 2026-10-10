import OAI.Probability.InvariantIsing.Magnetic.RestrictedFrameLogBound
import OAI.Probability.InvariantIsing.Magnetic.RestrictedRotationLogMean
import OAI.Probability.InvariantIsing.Magnetic.RestrictedProjectorPartition
import OAI.Probability.InvariantIsing.Cavity.CavityProjectorHaarMean

namespace OAI

/-! Integrability of the canonical base partition and the random-block
cavity logarithm under the product Haar law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma restricted_canonical_log_partition {N m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ) :
    restrictedProjectorLogPartition S hS T (fun a => t*lam a+2*perturbationScale N*v a) u
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)).1 =
    restrictedRotationLogMean S hS T
      (diagonalPerturbedEigenvalues
        (fun i => lam (Sum.elim (fun w => w.1) a₀ (e.symm i)))
        (cavityBaseGroup k e a₀) v t) (cavityBaseGroup k e a₀) u V := by
  rw [cavityCanonicalProjectorFrame_action_fst]
  exact restricted_projector_log_partition S hS _ V T lam v u t

lemma integrable_restricted_canonical_log_partition {N m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (t : ℝ) :
    Integrable (fun V => restrictedProjectorLogPartition S hS T
      (fun a => t*lam a+2*perturbationScale N*v a) u
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)).1) ν := by
  simp_rw [restricted_canonical_log_partition S hS k e a₀]
  exact integrable_restrictedRotationLogMean S hS ν T _ _ u hu

lemma restricted_canonical_capped_log_bound {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (A : CavityFactorBlocks d n) {D : ℝ}
    (hAb : cavityFactorSize A.1 A.2.1 A.2.2 ≤ D) :
    |restrictedProjectorCappedLog S hS C hC T (fun a => t*lam a+2*perturbationScale N*v a)
      u t cap δ A (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀))| ≤
        (|t| *D+|δ|)*(1+N) := by
  let g : Fin N → Fin m := fun i => Sum.elim (fun w => w.1) a₀ (e.symm i)
  let p := cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)
  have hp : p.1=fun a => cavitySpectralProjector V (cavitySpectralGroup g a) :=
    cavityCanonicalProjectorFrame_action_fst k e a₀ V
  have hFrame : p.2.transpose*p.2=1 := cavity_canonical_action_frame_gram k e a₀ V
  exact restricted_projector_capped_log_bound S hS C hC g V T lam v u hu t cap δ hcap A hAb p hp hFrame

lemma integrable_restricted_canonical_capped_log {Ω : Type*} [MeasurableSpace Ω]
    {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν]
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (t cap δ : ℝ) (hcap : 0 ≤ cap)
    (A : Ω → CavityFactorBlocks d n) (hA : Measurable A) {D : ℝ}
    (hAb : ∀ ω, cavityFactorSize (A ω).1 (A ω).2.1 (A ω).2.2 ≤ D) :
    Integrable (fun q : Ω × Orthogonal N => restrictedProjectorCappedLog S hS C hC T
      (fun a => t*lam a+2*perturbationScale N*v a) u t cap δ (A q.1)
      (cavityLabeledProjectorAction q.2 (cavityCanonicalProjectorFrame k e a₀))) (P.prod ν) := by
  have hp : Measurable (fun q : Ω × Orthogonal N =>
      cavityLabeledProjectorAction q.2 (cavityCanonicalProjectorFrame k e a₀)) :=
    (measurable_cavityCanonicalProjectorAction k e a₀).comp measurable_snd
  have hm := measurable_restrictedProjectorCappedLog S hS C hC T
    (fun a => t*lam a+2*perturbationScale N*v a) u t cap δ
    (fun q : Ω × Orthogonal N => A q.1) (hA.comp measurable_fst)
    (fun q : Ω × Orthogonal N =>
      cavityLabeledProjectorAction q.2 (cavityCanonicalProjectorFrame k e a₀)) hp
  apply Integrable.of_bound hm.aestronglyMeasurable ((|t| *D+|δ|)*(1+N))
  apply ae_of_all
  intro q
  rw [Real.norm_eq_abs]
  exact restricted_canonical_capped_log_bound S hS C hC k e a₀ q.2 T lam v u hu t cap δ hcap (A q.1) (hAb q.1)

end InvariantIsing

end

end OAI
