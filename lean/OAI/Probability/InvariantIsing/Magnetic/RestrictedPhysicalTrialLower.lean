import OAI.Probability.InvariantIsing.Magnetic.RestrictedCompressionCappedLog
import OAI.Probability.InvariantIsing.Magnetic.RestrictedRandomPressureIncrement
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFiniteTrialLower

namespace OAI

/-! The physical full-minus-base pressure increment bounds the exact
finite-field trial value from below. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem restricted_physical_trial_lower {m d n : ℕ} (hn₀ : 0<n)
    (N depth : ℕ → ℕ)
    (S : (r : ℕ) → Finset (Spin (N r))) (hS : ∀ r, (S r).Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (hN : ∀ r, 0<N r) (hNlim : Tendsto N atTop atTop)
    (g : (r : ℕ) → Fin (N r+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r))
    (ek : ∀ r a, {i : Fin (N r+n) // g r i=a} ≃ Fin (k r a+n))
    (es : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (l w : Fin m → ℕ → ℕ)
    (hg : ∀ r a i, g r i=a ↔ l a r ≤ i.val ∧ i.val<w a r)
    (hln : ∀ r a, l a r+n ≤ w a r) (hw : ∀ r a, w a r ≤ N r+n)
    (a₀ : Fin d → Fin m) (hk : ∀ r a, d ≤ k r a)
    (hgroups : ∀ r a, 0<cavityBaseGroupDimension (k r) a₀ a)
    (hdims : ∀ a, Tendsto (fun r => cavityBaseGroupDimension (k r) a₀ a) atTop atTop)
    (μ : (r : ℕ) → Measure (Orthogonal (N r+n))) [∀ r, IsProbabilityMeasure (μ r)] [∀ r, (μ r).IsMulRightInvariant]
    (ν : (r : ℕ) → Measure (Orthogonal (N r))) [∀ r, IsProbabilityMeasure (ν r)] [∀ r, (ν r).IsMulRightInvariant]
    (θ : (r : ℕ) → Measure (LabeledTree (depth r))) [∀ r, IsProbabilityMeasure (θ r)]
    (μG : (r : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k r) a₀ a)))
    [∀ r a, IsProbabilityMeasure (μG r a)] [∀ r a, (μG r a).IsMulRightInvariant]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ) (u : ℕ → ℕ → ℝ)
    (hv : ∀ r a, |v r a|≤2) (hu : ∀ r j, |u r j|≤2)
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
    (B : Matrix (Fin (m*n)) (Fin d) ℝ) (hB : B.transpose*B=1)
    (hBE : B.transpose*cavityLimitingStack (n := n) ρ=0)
    (hcomplete : B*B.transpose+cavityLimitingStack (n := n) ρ*
      (cavityLimitingStack (n := n) ρ).transpose=1)
    (amax : Fin m) (hmax : ∀ a, lam a≤lam amax)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a≤n)
    (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) 
    (hprob : ∀ ε>0, Tendsto (fun r => (μ r).real {U | ε<cavityFactorDeviation
      (cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
        (cavityCompressionGrams (g r) U))
      (B.transpose*cavityRepeatedSpectrum (n := n) lam*B-Matrix.diagonal (fun j => lam (a₀ j)),
       B.transpose*cavityRepeatedSpectrum (n := n) lam*cavityLimitingStack (n := n) ρ,
       (finiteR ρ lam hρ hρsum 0) • 1)}) atTop (𝓝 0)) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let Δ := fun r =>
      (∫ z, restrictedRotationLogMean (cavityProductSlice (S r) C) (cavityProductSlice_nonempty (S r) (hS r) C hC) z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
        (cavitySpectralGroup (g r)) (u r) z.1 ∂(μ r).prod (θ r)) -
      ∫ z, restrictedRotationLogMean (S r) (hS r) z.2
        (diagonalPerturbedEigenvalues
          (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e r).symm i)))
          (cavityBaseGroup (k r) (e r) a₀) (v r) 1)
        (cavityBaseGroup (k r) (e r) a₀) (u r) z.1 ∂(ν r).prod (θ r)
    ∀ ε>0, ∀ᶠ r in atTop,
      constrainedBlockValue C (cavityStrictUniformField ρ lam hρ hρsum p r)+
        fieldPairing (cavityStrictUniformPath p r) (cavityStrictUniformField ρ lam hρ hρsum p r)/2+
        spectralFunctional (finiteR ρ lam hρ hρsum) (cavityStrictUniformPath p r)-
        (n : ℝ)⁻¹*(Δ r+(Real.log C.card-n*Real.log 2)) < ε := by
  intro p Δ
  let A : CavityFactorBlocks d n :=
    (B.transpose*cavityRepeatedSpectrum (n := n) lam*B-Matrix.diagonal (fun j => lam (a₀ j)),
     B.transpose*cavityRepeatedSpectrum (n := n) lam*cavityLimitingStack (n := n) ρ,
     (finiteR ρ lam hρ hρsum 0) • 1)
  let AR := fun r U => cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
    (cavityCompressionGrams (g r) U)
  let δ := fun r => cavityDeterministicRate n m (2*(2*n+1)) (N r)+
    2*cavityCovarianceRate n (2*n+1) (N r)
  let cap := fun T r => ∫ ω,
    restrictedRandomHaarLog (S r) (hS r) C hC (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 T (δ r) (AR r) ω
      ∂((μ r).prod (((ν r).prod (θ r)).prod gaussianCoordinates)).prod (Measure.pi (μG r))
  have hbound : ∀ T>0, ∀ r, cap T r≤Δ r := by
    intro T hT r
    exact restricted_random_pressure_increment (hN r) (S r) (hS r) C hC (g r) (k r) (ek r) (e r) es B₀ a₀ (hk r)
      (Measure.pi (μG r)) (fun a => l a r) (fun a => w a r) (hg r) (hln r) (hw r)
      (μ r) (ν r) (θ r) lam (v r) (hv r) (u r) (hu r) 1 T hT.le
  have hcap T (hT : 0<T) := restricted_compression_capped_log_limit N depth S hS C hC hN hNlim g k e
    es B₀ a₀ hk hgroups hdims μ ν θ μG lam v u hc hfrac ρ hρ hρsum hρlim
    Q₀ hlim hgg hG d₀ hd0 hd hE hP hn hoff hdiag A hprob T hT.le
  exact restricted_cavity_finite_trial_preliminary_lower hn₀ C hC ρ lam hρ hρsum B hB hBE hcomplete a₀
    amax hmax counts hcounts_le hcounts hcounts_rho p Δ cap hbound hcap

end InvariantIsing

end

end OAI
