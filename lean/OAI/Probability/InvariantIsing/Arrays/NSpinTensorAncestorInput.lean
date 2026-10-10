import OAI.Probability.InvariantIsing.Arrays.NSpinTensorRetained
import OAI.Probability.IsingPerceptron.NormalizedRestrictionPi
import OAI.Probability.IsingPerceptron.SamplingIndependent

namespace OAI

/-!
The finite Ising tensor application of the conditional marked-path law.

The conditional marked-path law is the finite two-path specialization of
Panchenko--Talagrand, C. R. Acad. Sci. Paris I 345 (2007), 653--656,
Section 3, Lemma 3.1, equation (8), p.655, and Corollary 3.2, equation (9),
p.656. The mark spaces are complete separable metric spaces with their Borel
sigma algebras; ancestor conditional distributions may be arbitrary and
the measurable terminal need only satisfy `E exp X < infinity`.
The Gaussian-vector terminal satisfies this exponential integrability
hypothesis.
The law describes the joint branching and marks, including their
conditional ancestor distributions.

Averaging the fixed-root law gives the random-root law.
Forest edge `i` has shared mark exactly when `i < commonDepth`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- The published marking theorem's exponential integrability hypothesis
holds for the actual finite Ising terminal on a finite Gaussian path. -/
theorem tensorFinitePath_exp_integrable {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (z : SpinTensorIndex I degree → ℝ) :
    Integrable (fun w : Fin n → SpinTensorIndex I degree → ℝ =>
      Real.exp (spinTensorTerminal eig U c I degree amplitude (z + ∑ i, w i)))
      (Measure.pi (fun i : Fin n =>
        (tensorGaussianLaw I degree (v i) : Measure (SpinTensorIndex I degree → ℝ)))) := by
  obtain ⟨C, L, _, hL, hbound⟩ := spinTensorTerminal_linearGrowth eig U c I degree amplitude
  have hprod : Integrable (fun w : Fin n → SpinTensorIndex I degree → ℝ =>
      ∏ i, Real.exp (L * ‖w i‖))
      (Measure.pi (fun i : Fin n =>
        (tensorGaussianLaw I degree (v i) : Measure (SpinTensorIndex I degree → ℝ)))) :=
    Integrable.fintype_prod (f := fun (i : Fin n) (a : SpinTensorIndex I degree → ℝ) =>
      Real.exp (L * ‖a‖)) fun i => tensorGaussianLaw_moments hN I degree (v i) L
  apply (hprod.const_mul (Real.exp (C + L * ‖z‖))).mono'
    (((measurable_spinTensorTerminal eig U c I degree amplitude).comp
      (measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_pi_apply i))).exp.aestronglyMeasurable)
  apply ae_of_all
  intro w
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |spinTensorTerminal eig U c I degree amplitude (z + ∑ i, w i)| := le_abs_self _
    _ ≤ C + L * ‖z + ∑ i, w i‖ := hbound _
    _ ≤ C + L * (‖z‖ + ∑ i, ‖w i‖) := by
      apply add_le_add_right (mul_le_mul_of_nonneg_left _ hL)
      exact (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ = C + L * ‖z‖ + ∑ i, L * ‖w i‖ := by rw [mul_add, Finset.mul_sum]; ring

private lemma tensor_abs_integral_bound {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ] (f : A → ℝ) {C : ℝ}
    (hf : ∀ a, |f a| ≤ C) : |∫ a, f a ∂μ| ≤ C := by
  have hh : ∀ᵐ a ∂μ, ‖f a‖ ≤ C := ae_of_all _ fun a => by
    simpa only [Real.norm_eq_abs] using hf a
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f) hh

/-- Iterated conditional expectation of two Gaussian increment paths. Before
their branching depth the two paths receive the same tilted increment;
afterwards their next increments are conditionally independent. -/
def tensorAncestorPairPathMean {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (d : ℕ) :
    (q : ℕ) → ℕ → (SpinTensorIndex I degree → ℝ) → (SpinTensorIndex I degree → ℝ) →
      ((Fin q → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) → ℝ) → ℝ
  | 0, _, _, _, F => F Fin.elim0
  | q + 1, i, z₁, z₂, F =>
      if i < d then
        ∫ a, tensorAncestorPairPathMean eig U c I degree amplitude n b v d q (i + 1)
          (z₁ + a) (z₂ + a) (fun w => F (Fin.cons (a, a) w))
          ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z₁
      else
        ∫ a₁, ∫ a₂, tensorAncestorPairPathMean eig U c I degree amplitude n b v d q (i + 1)
          (z₁ + a₁) (z₂ + a₂) (fun w => F (Fin.cons (a₁, a₂) w))
          ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z₂
          ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z₁

theorem tensorAncestorPairPathMean_abs_le {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (d q i : ℕ)
    (z₁ z₂ : SpinTensorIndex I degree → ℝ)
    (F : (Fin q → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) → ℝ)
    {C : ℝ} (hF : ∀ w, |F w| ≤ C) :
    |tensorAncestorPairPathMean eig U c I degree amplitude n b v d q i z₁ z₂ F| ≤ C := by
  induction q generalizing i z₁ z₂ with
  | zero => exact hF _
  | succ q ih =>
      have := tensorAncestorMarkKernel_markov hN eig U c I degree amplitude n b v hb i
      dsimp only [tensorAncestorPairPathMean]
      split_ifs
      · apply tensor_abs_integral_bound
        intro a
        exact ih (i + 1) (z₁ + a) (z₂ + a)
          (fun w => F (Fin.cons (a, a) w)) (fun w => hF _)
      · have hinner (a₁ : SpinTensorIndex I degree → ℝ) :
            |∫ a₂, tensorAncestorPairPathMean eig U c I degree amplitude n b v d q (i + 1)
              (z₁ + a₁) (z₂ + a₂) (fun w => F (Fin.cons (a₁, a₂) w))
              ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z₂| ≤ C := by
          apply tensor_abs_integral_bound
          intro a₂
          exact ih (i + 1) (z₁ + a₁) (z₂ + a₂)
            (fun w => F (Fin.cons (a₁, a₂) w)) (fun w => hF _)
        exact tensor_abs_integral_bound _ hinner

/-- The actual tilted two-leaf Gaussian path expectation, with the spin
residual integrated in the finite Ising terminal. -/
def tensorTiltedPairPathMean {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (z : SpinTensorIndex I degree → ℝ)
    (Φ : ℕ × (Fin n → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) → ℝ) : ℝ :=
  ∫ p : TensorCoordinateData I degree n,
    referenceReplicaMean (labeledLeafLaw n p.1)
      (fun α => spinTensorTerminal eig U c I degree amplitude
        (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n p.2) α z))
      (fun σ : Fin 2 → LabeledLeaf n => Φ
        (labeledCommonDepth n (σ 0) (σ 1),
          fun i => (p.2 (edgeAt n (σ 0) i), p.2 (edgeAt n (σ 1) i))))
    ∂tensorCoordinateLaw I degree n b v

/-- The exact finite tensor specialization of the published joint marked
path law. The unperturbed cascade supplies the shared-prefix depth and
the normalized ancestor kernels supply the conditional marks. -/
def TensorAncestorPairLaw {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) : Prop :=
  ∀ z : SpinTensorIndex I degree → ℝ,
  ∀ Φ : ℕ × (Fin n → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) → ℝ,
    Measurable Φ → (∃ C : ℝ, ∀ p, |Φ p| ≤ C) →
      tensorTiltedPairPathMean eig U c I degree amplitude n b v z Φ =
        ∫ α : ℕ → LabeledLeaf n,
          tensorAncestorPairPathMean eig U c I degree amplitude n b v
            (labeledCommonDepth n (α 0) (α 1)) n 0 z z
            (fun w => Φ (labeledCommonDepth n (α 0) (α 1), w))
          ∂cascadeReplicaLaw n b

/-- Conditional two-path marking law for finite hierarchical tensor fields. -/
def PanchenkoTalagrandTensorPairInput : Prop :=
  ∀ N m k : ℕ, 0 < N →
  ∀ (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0),
    CascadeExponents n b → TensorAncestorPairLaw eig U c I degree amplitude n b v

/-- The independent root Gaussian is averaged after the fixed-root path
identity. Root level zero and forest levels one through `n` agree with
the flat tensor coefficient convention. -/
theorem tensorRootedPairPath_identity (hpub : PanchenkoTalagrandTensorPairInput)
    {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b)
    (Φ : (SpinTensorIndex I degree → ℝ) ×
      (ℕ × (Fin n → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ))) → ℝ)
    (hΦ : Measurable Φ) (hΦb : ∃ C : ℝ, ∀ p, |Φ p| ≤ C) :
    (∫ z, tensorTiltedPairPathMean eig U c I degree amplitude n b (fun i => v (i + 1)) z
      (fun p => Φ (z, p))
      ∂(tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))) =
      ∫ z, ∫ α : ℕ → LabeledLeaf n,
        tensorAncestorPairPathMean eig U c I degree amplitude n b (fun i => v (i + 1))
          (labeledCommonDepth n (α 0) (α 1)) n 0 z z
          (fun w => Φ (z, labeledCommonDepth n (α 0) (α 1), w))
        ∂cascadeReplicaLaw n b
      ∂(tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)) := by
  apply integral_congr_ae
  apply ae_of_all
  intro z
  apply hpub N m k hN eig U c I degree amplitude n b (fun i => v (i + 1)) hb z
  · exact hΦ.comp (measurable_const.prodMk measurable_id)
  · obtain ⟨C, hC⟩ := hΦb
    exact ⟨C, fun p => hC (z, p)⟩

end InvariantIsing

end

end OAI
