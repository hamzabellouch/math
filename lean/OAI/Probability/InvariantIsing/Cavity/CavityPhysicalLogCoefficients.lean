import OAI.Probability.InvariantIsing.Cavity.CavityHaarPenalizedLimit
import OAI.Probability.InvariantIsing.Cavity.CavityHaarLogObservable
import OAI.Probability.InvariantIsing.Cavity.CavityRotationVectorNorm
import OAI.Probability.InvariantIsing.Cavity.CavityRotationProbability

namespace OAI

/-! Logarithmic coefficient replacement specialized to the actual
base-system Gibbs probability and its physical spectral-group vectors. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_physical_penalized_log_coefficients {m q d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ r, 0<N r)
    (dims : ℕ → Fin m → ℕ) (hgroups : ∀ r a, 0<dims r a)
    (E : (r : ℕ) → ((a : Fin m) × Fin (dims r a)) ≃ Fin (N r))
    (μ : (r : ℕ) → Measure (Orthogonal (N r))) [∀ r, IsProbabilityMeasure (μ r)]
    (θ : (r : ℕ) → Measure (LabeledTree (depth r))) [∀ r, IsProbabilityMeasure (θ r)]
    (μG : (r : ℕ) → (a : Fin m) → Measure (Orthogonal (dims r a)))
    [∀ r a, IsProbabilityMeasure (μG r a)] [∀ r a, (μG r a).IsMulRightInvariant]
    (A₀ : (r : ℕ) → (a : Fin m) → Matrix (Fin (dims r a)) (Fin q) ℝ)
    (hA₀ : ∀ r a, (A₀ r a).transpose*A₀ r a=1)
    (eig : (r : ℕ) → Fin (N r) → ℝ) (u : ℕ → ℕ → ℝ)
    {c : ℝ} (hc : 0<c) (hfrac : ∀ r a, c ≤ (dims r a : ℝ)/N r)
    (Z : ℕ → Type*) [∀ r, MeasurableSpace (Z r)]
    (P : (r : ℕ) → Measure (Z r)) [∀ r, IsProbabilityMeasure (P r)]
    (A : (r : ℕ) → Z r → CavityFactorBlocks d n) (hA : ∀ r, Measurable (A r))
    (A₁ : CavityFactorBlocks d n) {D : ℝ} (hD : 0≤D)
    (hAb : ∀ r z, cavityFactorSize (A r z).1 (A r z).2.1 (A r z).2.2 ≤ D)
    (hA₁ : cavityFactorSize A₁.1 A₁.2.1 A₁.2.2 ≤ D)
    (hprob : ∀ ε>0, Tendsto (fun r => (P r).real
      {z | ε<cavityFactorDeviation (A r z) A₁}) atTop (𝓝 0))
    (f : Fin d → Fin m × Fin q) (cap : ℝ) (hcap : 0≤cap)
    (δ : ℕ → ℝ) (hδ : ∀ r, 0≤δ r) (hδlim : Tendsto δ atTop (𝓝 0)) :
    let ν := fun r => cavityRotationProbability (depth := depth r) (eig r)
      (cavitySpectralGroup (fun i => ((E r).symm i).1)) (u r)
    let vectors := fun r => cavityRotationVectors (depth := depth r) (dims r) (E r)
    let Q := fun r => ((P r).prod (((μ r).prod (θ r)).prod gaussianCoordinates)).prod
      (Measure.pi (μG r))
    Tendsto (fun r =>
      (∫ ω, cavityHaarLogObservable (fun z => ν r z.2) f (fun z => vectors r z.2)
        (A₀ r) (fun z => A r z.1) 1 cap (δ r) ω ∂Q r) -
      ∫ ω, cavityHaarLogObservable (fun z => ν r z.2) f (fun z => vectors r z.2)
        (A₀ r) (fun _ => A₁) 1 cap 0 ω ∂Q r) atTop (𝓝 0) := by
  intro ν vectors Q
  let Ω := fun r => Z r × ((Orthogonal (N r) × LabeledTree (depth r)) × (ℕ → ℝ))
  let X := fun r => Spin (N r) × LabeledLeaf (depth r)
  let P₀ := fun r => (P r).prod (((μ r).prod (θ r)).prod gaussianCoordinates)
  let ν₀ := fun r (ω : Ω r) => ν r ω.2
  let v₀ := fun r (ω : Ω r) => vectors r ω.2
  let A₂ := fun r (ω : Ω r) => A r ω.1
  have hmν r : Measurable (ν₀ r) :=
    (measurable_cavityRotationProbability _ _ _).comp measurable_snd
  have hmv r x : Measurable (fun ω a => v₀ r ω a x) :=
    (measurable_cavityRotationVectors (dims r) (E r) x).comp measurable_snd
  have hnorm r (ω : Ω r) x a :
      ‖(WithLp.toLp 2 (v₀ r ω a x) : EuclideanSpace ℝ (Fin (dims r a)))‖^2 ≤
        (1/c)*dims r a :=
    cavity_rotation_vectors_norm_bound (hN r) (dims r) (hgroups r) (E r) hc (hfrac r) ω.2 x a
  have hmA r : Measurable (A₂ r) := (hA r).comp measurable_fst
  have hp : ∀ ε>0, Tendsto (fun r => (P₀ r).real
      {ω | ε<cavityFactorDeviation (A₂ r ω) A₁}) atTop (𝓝 0) := by
    intro ε hε
    apply (hprob ε hε).congr
    intro r
    exact (cavity_factor_deviation_pullback (P₀ r) (P r) Prod.fst
      measurePreserving_fst (A r) (hA r) A₁ ε).symm
  have h := cavity_haar_penalized_coefficient_limit dims hgroups μG Ω X P₀ ν₀ hmν
    f v₀ hmv A₀ hA₀ (div_nonneg zero_le_one hc.le) hnorm A₂ hmA A₁ hD
    (fun r ω => hAb r ω.1) hA₁ hp (uniformSpinPrior n) cap hcap δ hδ hδlim
  simpa only [cavityHaarLogObservable, ν₀, v₀, A₂, P₀, Q, one_mul, zero_mul, sub_zero] using h

end InvariantIsing

end

end OAI
