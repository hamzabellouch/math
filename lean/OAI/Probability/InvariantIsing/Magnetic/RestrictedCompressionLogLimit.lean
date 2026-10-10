import OAI.Probability.InvariantIsing.Magnetic.RestrictedCanonicalLogCoefficients
import OAI.Probability.InvariantIsing.Cavity.CavityCompressionFactorBound
import OAI.Probability.InvariantIsing.Cavity.CavityActualErrorRates

namespace OAI

/-! The actual random compression and its explicit geometric error give
the canonical logarithm with fixed coefficients in the large-system limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem restricted_compression_log_limit {m d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (r : ℕ) → Finset (Spin (N r))) (hS : ∀ r, (S r).Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (hN : ∀ r, 0<N r) (hNlim : Tendsto N atTop atTop)
    (g : (r : ℕ) → Fin (N r+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r))
    (es : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) (hk : ∀ r a, d ≤ k r a)
    (hgroups : ∀ r a, 0<cavityBaseGroupDimension (k r) a₀ a)
    (μ : (r : ℕ) → Measure (Orthogonal (N r+n)))
    [∀ r, IsProbabilityMeasure (μ r)]
    (ν : (r : ℕ) → Measure (Orthogonal (N r))) [∀ r, IsProbabilityMeasure (ν r)]
    (θ : (r : ℕ) → Measure (LabeledTree (depth r))) [∀ r, IsProbabilityMeasure (θ r)]
    (μG : (r : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k r) a₀ a)))
    [∀ r a, IsProbabilityMeasure (μG r a)] [∀ r a, (μG r a).IsMulRightInvariant]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ) (u : ℕ → ℕ → ℝ)
    {c : ℝ} (hc : 0<c)
    (hfrac : ∀ r a, c ≤ (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r)
    (A₁ : CavityFactorBlocks d n)
    (hprob : ∀ ε>0, Tendsto (fun r => (μ r).real {U | ε<cavityFactorDeviation
      (cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
        (cavityCompressionGrams (g r) U)) A₁}) atTop (𝓝 0))
    (cap : ℝ) (hcap : 0≤cap) :
    let A := fun r U => cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
      (cavityCompressionGrams (g r) U)
    let δ := fun r => cavityDeterministicRate n m (2*(2*n+1)) (N r)+
      2*cavityCovarianceRate n (2*n+1) (N r)
    Tendsto (fun r =>
      (∫ p, restrictedRandomHaarLog (S r) (hS r) C hC (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap (δ r) (A r) p
        ∂((μ r).prod (((ν r).prod (θ r)).prod gaussianCoordinates)).prod (Measure.pi (μG r))) -
      ∫ p, restrictedCanonicalHaarLog (S r) (hS r) C hC (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap 0 A₁ p
        ∂(((ν r).prod (θ r)).prod gaussianCoordinates).prod (Measure.pi (μG r))) atTop (𝓝 0) := by
  intro A δ
  let D₀ := ((d : ℝ)*d+d*n+n*n)*cavityMatrixMass (cavityRepeatedSpectrum (n := n) lam)+
    cavityMatrixMass (Matrix.diagonal (fun j => lam (a₀ j)))
  let D := max D₀ (cavityFactorSize A₁.1 A₁.2.1 A₁.2.2)
  have hD : 0≤D := (cavityFactorSize_nonneg A₁.1 A₁.2.1 A₁.2.2).trans (le_max_right _ _)
  have hA r : Measurable (A r) :=
    (measurable_cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀).comp
      (measurable_cavityCompressionGrams (g r))
  have hAb r U : cavityFactorSize (A r U).1 (A r U).2.1 (A r U).2.2 ≤ D :=
    (cavity_compression_factor_size_bound (g r) es lam (fun j => lam (a₀ j)) B₀ U).trans
      (le_max_left _ _)
  have hδ r : 0≤δ r := by
    dsimp only [δ]
    have hd : 0≤cavityDeterministicRate n m (2*(2*n+1)) (N r) := by
      unfold cavityDeterministicRate perturbationScale
      positivity
    exact add_nonneg hd (mul_nonneg (by norm_num)
      (cavityCovarianceRate_nonneg n (by positivity) (N r)))
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have ht := ((cavityDeterministicRate_tendsto n m (2*(2*n+1))).comp hNlim).add
      (((cavityCovarianceRate_tendsto n (2*n+1)).comp hNlim).const_mul 2)
    simpa only [δ, Function.comp_def, mul_zero, add_zero] using ht
  exact restricted_canonical_log_coefficients N depth S hS C hC hN k e a₀ hk hgroups ν θ μG lam v u
    hc hfrac (fun r => Orthogonal (N r+n)) μ A hA A₁ hD hAb (le_max_right _ _)
    hprob cap hcap δ hδ hδlim

end InvariantIsing

end

end OAI
