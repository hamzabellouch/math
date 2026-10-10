import OAI.Probability.InvariantIsing.Cavity.CavityOriginalEntropyLimit
import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalTrialLower
import OAI.Probability.InvariantIsing.Cavity.CavityVariationalTrialLower

namespace OAI

/-! The original physical model satisfies the finite-spectrum variational
lower bound along a spectral/GG/Ward subsequence. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators

namespace InvariantIsing

theorem cavity_physical_variational_lower (hpub : PanchenkoTalagrandFieldPairInput) {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : (j : ℕ) → Measure (LabeledTree (depth j))) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2)
    (good : (j : ℕ) → Set (SpecialOrthogonal (N j+n)))
    (hgood : ∀ j, MeasurableSet (good j))
    (hp : Tendsto (fun j => ((μ j).map (cavityOrientationLift
      (Nat.add_pos_left (hN j) n))).real (good j)) atTop (𝓝 1))
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ j U, U ∈ good j → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g j) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
    (hd : 0 < d) (hn : 0 < n)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
    (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
    (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
    {c : ℝ} (hc : 0 < c)
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j)
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j) atTop (𝓝 ρ))
    (A_ : CavityFactorBlocks d n)
    (hA : A_ = ((cavityCompressionLimitFrame es B₀).transpose *
      cavityRepeatedSpectrum (n := n) lam * cavityCompressionLimitFrame es B₀ -
      Matrix.diagonal (fun i => lam (a₀ i)),
      (cavityCompressionLimitFrame es B₀).transpose * cavityRepeatedSpectrum (n := n) lam *
        cavityLimitingStack (n := n) ρ,
      (finiteR ρ lam hρ hρsum 0) • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A_}) atTop (𝓝 0))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun j => cavityRotationArrayLaw (ν j) (θ j)
      (diagonalPerturbedEigenvalues
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (v j) 1)
      (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (u j))
      atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m+1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralGram x)
    (δ : Fin (m+1) → ℝ) (hδ0 : ∀ j, 0 ≤ δ j)
    (hδ : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ i j, (x (i,i) j : ℝ) = δ j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m+1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x)
    (hnonneg : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ lam j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ lam j l = 0)
    (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a≤n)
    (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) (R : Rotation n) :
    let Δ := fun r =>
      (∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
        (cavitySpectralGroup (g r)) (u r) z.1 ∂(μ r).prod (θ r)) -
      ∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues
          (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e r).symm i)))
          (cavityBaseGroup (k r) (e r) a₀) (v r) 1)
        (cavityBaseGroup (k r) (e r) a₀) (u r) z.1 ∂(ν r).prod (θ r)
    ∀ ε>0, ∀ᶠ r in atTop,
      (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal-(n : ℝ)⁻¹*Δ r<ε := by
  intro Δ
  let p := spectralSpinQuantilePath Q₀ hP hnonneg
  let B := cavityCompressionLimitFrame es B₀
  have hprob' := hprob
  rw [hA] at hprob'
  have hlower := cavity_physical_trial_lower hn N depth hN hNlim g k e ek es B₀
    (fun a r => l r a) (fun a r => w r a) hg hln hw a₀ hk hgroups hdims μ ν θ μG
    lam v u hv hu hc hcG ρ hρ hρsum hρlim Q₀ hlim hgg hG δ hδ0 hδ hE hP hnonneg
    hoff hdiag B (cavityCompressionLimitFrame_gram es B₀ hB₀)
    (cavityCompressionLimitFrame_perp es B₀ ρ (fun a => (hρ a).le) hperp)
    (cavityCompressionLimitFrame_complete es B₀ hB₀ ρ (fun a => (hρ a).le) hρsum hperp)
    a ha counts hcounts_le hcounts hcounts_rho R hprob'
  obtain ⟨hent,hconv⟩ := cavity_original_entropy_trial_limit hpub N depth hN hNlim g k ek e
    es B₀ a₀ hk μG l w hg hln hw μ ν θ lam v hv u hu good hgood hp hL hbound hd hn hB₀
    ρ hρ hρsum hperp hgroups hdims hc hcG hρlim A_ hA hprob Q₀ hlim hgg hG δ hδ0 hδ hE hP
    hnonneg hoff hdiag a ha
  exact cavity_variational_lower_of_trial_limit ρ lam hρ hρsum p
    (fun r => fieldValue (cavityStrictUniformField ρ lam hρ hρsum p r) 0+
      fieldPairing (cavityStrictUniformPath p r) (cavityStrictUniformField ρ lam hρ hρsum p r)/2+
      spectralFunctional (finiteR ρ lam hρ hρsum) (cavityStrictUniformPath p r))
    (fun r => (n : ℝ)⁻¹*Δ r) hent hconv hlower

end InvariantIsing

end

end OAI
