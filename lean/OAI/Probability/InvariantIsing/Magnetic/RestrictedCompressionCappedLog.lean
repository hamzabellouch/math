import OAI.Probability.InvariantIsing.Magnetic.RestrictedCanonicalLogLimit
import OAI.Probability.InvariantIsing.Magnetic.RestrictedCompressionLogLimit

namespace OAI

/-! The actual random-compression pressure integrand converges to the
finite cascade logarithm, including its vanishing geometric penalty. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem restricted_compression_capped_log_limit {m d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (r : ℕ) → Finset (Spin (N r))) (hS : ∀ r, (S r).Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (hN : ∀ r, 0<N r) (hNlim : Tendsto N atTop atTop)
    (g : (r : ℕ) → Fin (N r+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r))
    (es : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) (hk : ∀ r a, d ≤ k r a)
    (hgroups : ∀ r a, 0<cavityBaseGroupDimension (k r) a₀ a)
    (hdims : ∀ a, Tendsto (fun r => cavityBaseGroupDimension (k r) a₀ a) atTop atTop)
    (μ : (r : ℕ) → Measure (Orthogonal (N r+n))) [∀ r, IsProbabilityMeasure (μ r)]
    (ν : (r : ℕ) → Measure (Orthogonal (N r))) [∀ r, IsProbabilityMeasure (ν r)]
    (θ : (r : ℕ) → Measure (LabeledTree (depth r))) [∀ r, IsProbabilityMeasure (θ r)]
    (μG : (r : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k r) a₀ a)))
    [∀ r a, IsProbabilityMeasure (μG r a)] [∀ r a, (μG r a).IsMulRightInvariant]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ) (u : ℕ → ℕ → ℝ)
    {c : ℝ} (hc : 0<c)
    (hfrac : ∀ r a, c ≤ (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0<ρ a) (hρsum : ∑ a, ρ a=1)
    (hρlim : Tendsto (fun r a => (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r) atTop (𝓝 ρ))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun r => restrictedRotationArrayLaw (S r) (hS r) (ν r) (θ r)
      (diagonalPerturbedEigenvalues
        (fun i => lam ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1)) (v r) 1)
      (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1))
      (u r)) atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m+1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralGram x)
    (d₀ : Fin (m+1) → ℝ) (hd0 : ∀ j, 0≤d₀ j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ i j, (x (i,i) j : ℝ)=d₀ j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ j, 0≤(x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ t, |Φ t|≤B) →
      spectralOffWardResidual Q₀ ρ lam j l Φ=0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ lam j l=0)
    (A : CavityFactorBlocks d n)
    (hprob : ∀ ε>0, Tendsto (fun r => (μ r).real {U | ε<cavityFactorDeviation
      (cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
        (cavityCompressionGrams (g r) U)) A}) atTop (𝓝 0))
    (cap : ℝ) (hcap : 0≤cap) :
    let AR := fun r U => cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
      (cavityCompressionGrams (g r) U)
    let δ := fun r => cavityDeterministicRate n m (2*(2*n+1)) (N r)+
      2*cavityCovarianceRate n (2*n+1) (N r)
    let p := spectralSpinQuantilePath Q₀ hP hn
    let Qf := fun r => cavityLabeledDisorderLaw r (chainExponent (uniformCut r))
      (cavityFiniteRootCovariance ρ lam hρ hρsum a₀ (cavityStrictUniformPath p r)
        (cavityStrictUniformLevels p r))
      (cavityFiniteNoiseCovariance ρ lam hρ hρsum a₀ (cavityStrictUniformPath p r)
        (uniformCut r) (cavityStrictUniformLevels p r))
    let η := fun r => cavityLabeledPriorKernel r
      (cavityFiniteCovariancePath ρ lam hρ hρsum a₀ (cavityStrictUniformPath p r)
        (cavityStrictUniformLevels p r) r) (restrictedSpinPrior C hC)
    Tendsto (fun r =>
      (∫ ω, restrictedRandomHaarLog (S r) (hS r) C hC (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap (δ r) (AR r) ω
        ∂((μ r).prod (((ν r).prod (θ r)).prod gaussianCoordinates)).prod (Measure.pi (μG r))) -
      ∫ ω, Real.log (∫ x, Real.exp (min (cavityLabeledPotential r A.1 A.2.1 A.2.2 (ω,x)) cap)
        ∂η r ω) ∂Qf r) atTop (𝓝 0) := by
  intro AR δ p Qf η
  have hc₀ := restricted_compression_log_limit N depth S hS C hC hN hNlim g k e es B₀ a₀ hk hgroups
    μ ν θ μG lam v u hc hfrac A hprob cap hcap
  have hf := restricted_canonical_capped_log_limit N depth S hS C hC hN k e a₀ hk hgroups hdims
    ν θ μG lam v u hc hfrac ρ hρ hρsum hρlim Q₀ hlim hgg hG d₀ hd0 hd hE hP hn
    hoff hdiag A cap hcap
  have ht := hc₀.add hf
  simpa only [sub_add_sub_cancel, add_zero] using ht

end InvariantIsing

end

end OAI
