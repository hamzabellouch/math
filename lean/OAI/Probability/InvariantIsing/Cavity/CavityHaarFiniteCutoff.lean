import OAI.Probability.InvariantIsing.Cavity.CavityHaarRestrictedRegularized
import OAI.Probability.InvariantIsing.Cavity.CavityHaarRestrictedFloor
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteRestrictedError
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffFloorLimit
import OAI.Probability.InvariantIsing.Cavity.CavityHaarSpinNumerator

namespace OAI

/-! The actual Haar restricted Gibbs test approaches the full finite
spectral cavity test as the cutoff grows after the system-size limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_finite_cutoff_comparison {m r q dim kspin : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (Ω X : ℕ → Type*) [∀ k, MeasurableSpace (Ω k)] [∀ k, MeasurableSpace (X k)]
    [∀ k, Countable (X k)] [∀ k, MeasurableSingletonClass (X k)]
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (ν : (k : ℕ) → Ω k → Measure (X k)) (hν : ∀ k, Measurable (ν k))
    [∀ k ω, IsProbabilityMeasure (ν k ω)]
    (B : (k : ℕ) → Ω k → X k → X k → SpectralEntry (m + 1))
    (hB : ∀ k x y, Measurable (fun ω => B k ω x y))
    (hGram : ∀ k x, SpectralGram (cavitySampledEntryArray (B k) x))
    (v₀ : (k : ℕ) → Ω k → (j : Fin m) → X k → Fin (N k j) → ℝ)
    (hvM : ∀ k x, Measurable (fun ω j => v₀ k ω j x))
    (C : ℝ)
    (hv : ∀ s k (x : Ω k × (ℕ → X k)) j (i l : Fin s), |cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i)) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ s k (x : Ω k × (ℕ → X k)), cavityGroupReplicaCovariance q (cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i))) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) s (cavitySampledEntryArray (B k) x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (disorderReplicaLaw (P k) (ν k) (hν k)).map (cavitySampledEntryArray (B k)))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (d : Fin (m + 1) → ℝ) (hd0 : ∀ j, 0 ≤ d j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = d j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ eig j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ eig j l = 0)
    (g : Fin dim → Fin m) (e : Fin dim → Fin m × Fin q)
    (he : Function.Injective e) (heg : ∀ j, (e j).1 = g j)
    (K : Matrix (Fin dim) (Fin dim) ℝ) (L : Matrix (Fin dim) (Fin kspin) ℝ)
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ)
    (π : Measure (Spin kspin)) [IsProbabilityMeasure π]
    (Fspin : SpectralBlock m r × (Fin r → Spin kspin) →ᵇ ℝ)
    (hNpos : ∀ n a, 0 < N n a) (hC : 0 ≤ C)
    {N₀ : ℕ} (B₀ : Matrix (Fin (m*N₀)) (Fin dim) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (hK : K = B₀.transpose * cavityRepeatedSpectrum (n := N₀) eig * B₀ -
      Matrix.diagonal (fun i => eig (g i)))
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop)
    (hnull : ∀ j s, (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m s) : Measure
      (SpectralBlock m s × EuclideanSpace ℝ (Fin m × (Fin s × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let τ := fun j => cavityFactorSize K L Cspin * (1+(b j)^2)
    let η := fun n => cavityLabeledPriorKernel n
      (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n) n) π
    let Qf := fun n => cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
      (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n))
      (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p n)
        (uniformCut n) (cavityStrictUniformLevels p n))
    let Of := fun n => cavityFiniteReplicaSpectralBlock ρ eig hρ hρsum (cavityStrictUniformPath p n)
      (cavityStrictUniformLevels p n)
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      |(∫ ω, cavityWeightedReplicaMean ((ν n ω.1).prod π)
          (fun x => cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin (τ j) (b j) (ω,x))
          (cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1) Fspin)
          ∂(P n).prod (Measure.pi (μ n))) -
        ∫ ω, cavityWeightedReplicaMean (η n ω)
          (fun x => Real.exp (cavityLabeledPotential n K L Cspin (ω,x)))
          (fun σ => cavityLabeledReplicaTest (Of n) Fspin (ω,σ)) ∂Qf n| < ε := by
  intro p τ η Qf Of
  let f j n := ∫ ω, cavityWeightedReplicaMean ((ν n ω.1).prod π)
    (fun x => cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin (τ j) (b j) (ω,x))
    (cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1) Fspin)
    ∂(P n).prod (Measure.pi (μ n))
  let u j δ n := ∫ ω, cavityRegularizedReplicaMean ((ν n ω.1).prod π)
    (fun x => cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin (τ j) (b j) (ω,x))
    (cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1) Fspin) δ
    ∂(P n).prod (Measure.pi (μ n))
  let v j δ n := ∫ ω, cavityRegularizedReplicaMean (η n ω)
    (fun x => cavityLabeledRestrictedWeight n K L Cspin (τ j) (b j) (ω,x))
    (fun σ => cavityLabeledReplicaTest (Of n) Fspin (ω,σ)) δ ∂Qf n
  let z n := ∫ ω, cavityWeightedReplicaMean (η n ω)
    (fun x => Real.exp (cavityLabeledPotential n K L Cspin (ω,x)))
    (fun σ => cavityLabeledReplicaTest (Of n) Fspin (ω,σ)) ∂Qf n
  let M₁ := (dim : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2
  let M₂ := cavityGaussianLinearMomentBound dim 4 0 (∑ a, (ρ a)⁻¹)
  let M₃ := cavityGaussianLinearMomentBound dim 2
    (cavityMatrixMass L + cavityMatrixMass Cspin) (ρ a)⁻¹
  let E j := |4 * ‖Fspin‖ * (M₁ / (b j)^4)| +
    |4 * ‖Fspin‖ * (M₂ / (b j)^4) + 2 * ‖Fspin‖ * r * (M₃ / (b j)^2)|
  have hnorm n ω x a :
      ‖(WithLp.toLp 2 (v₀ n ω a x) : EuclideanSpace ℝ (Fin (N n a)))‖^2 ≤ C * N n a :=
    cavity_group_gram_diagonal_norm (hNpos n) (fun a => v₀ n ω a x)
      (fun a => hv 1 n (ω,fun _ => x) a 0 0) a
  have hu j δ (hδ : 0 < δ) n : |f j n - u j δ n| ≤
      (‖Fspin‖ * r) * δ / (Real.exp (-τ j)/2) + E j := by
    have hh := cavity_haar_restricted_floor_error (P n) (ν n) (hν n) (hNpos n) (μ n)
      e (v₀ n) (hvM n) (A₀ n) (hA₀ n) hC (hnorm n)
      (cavitySampledGroupBlock (B n)) (measurable_cavitySampledGroupBlock (B n) (hB n))
      K L Cspin π (τ j) (hb j) hδ.le (le_refl _) Fspin
    rw [abs_sub_comm] at hh
    have hh' : |f j n-u j δ n| ≤ (‖Fspin‖*r)*δ/(Real.exp (-τ j)/2) +
        4*‖Fspin‖*(M₁/(b j)^4) := by
      simpa only [f,u,τ,M₁,neg_mul] using hh
    apply hh'.trans
    dsimp only [E]
    linarith [le_abs_self (4*‖Fspin‖*(M₁/(b j)^4)),
      abs_nonneg (4*‖Fspin‖*(M₂/(b j)^4)+2*‖Fspin‖*r*(M₃/(b j)^2))]
  have hvz j δ (hδ : 0 < δ) n : |v j δ n-z n| ≤
      (‖Fspin‖ * r) * δ / (Real.exp (-τ j)/2) + E j := by
    have hh := cavity_finite_restricted_error ρ eig hρ hρsum B₀ hB₀ g a ha p L Cspin π
      (Of n) Fspin (τ j) (hb j) hδ.le
    simp only [← hK] at hh
    have hh' := hh (le_refl _)
    have hh'' : |v j δ n-z n| ≤ (‖Fspin‖*r)*δ/(Real.exp (-τ j)/2) +
        4*‖Fspin‖*(M₂/(b j)^4) + 2*‖Fspin‖*r*(M₃/(b j)^2) := by
      simpa only [v,z,η,Qf,M₂,M₃,τ,neg_mul] using hh'
    apply hh''.trans
    dsimp only [E]
    linarith [abs_nonneg (4*‖Fspin‖*(M₁/(b j)^4)),
      le_abs_self (4*‖Fspin‖*(M₂/(b j)^4)+2*‖Fspin‖*r*(M₃/(b j)^2))]
  have huv j δ (hδ : 0 < δ) : Tendsto (fun n => u j δ n-v j δ n) atTop (𝓝 0) := by
    exact cavity_haar_restricted_gibbs_regularized_match N hN μ A₀ hA₀ Ω X P ν hν B hB
      hGram v₀ hvM C hv ρs ρ eig hρs hρ hρlim hρsum hcov Q Q₀ hQ hlim hgg hG
      d hd0 hd hE hP hn hoff hdiag g e he heg K L Cspin (τ j) δ hδ π Fspin
      (hb j).le (hnull j)
  have hinv : Tendsto (fun j => (b j)⁻¹) atTop (𝓝 (0:ℝ)) := tendsto_inv_atTop_zero.comp hblim
  have hE0 : Tendsto E atTop (𝓝 0) := by
    have ht := (((hinv.pow 4).const_mul (4*‖Fspin‖*M₁)).abs).add
      ((((hinv.pow 4).const_mul (4*‖Fspin‖*M₂)).add
        ((hinv.pow 2).const_mul (2*‖Fspin‖*r*M₃))).abs)
    simpa only [E,div_eq_mul_inv,inv_pow,mul_assoc,zero_pow (by decide : 4 ≠ 0),
      zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,abs_zero] using ht
  exact cavity_cutoff_floor_comparison f z u v (fun j => Real.exp (-τ j)/2) E
    (mul_nonneg (norm_nonneg Fspin) (Nat.cast_nonneg r)) (fun _ => by positivity)
    hE0 hu hvz huv

end InvariantIsing

end

end OAI
