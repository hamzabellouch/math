import OAI.Probability.InvariantIsing.Magnetic.RestrictedHaarFiniteOverlap
import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalOverlapCutoff
import OAI.Probability.InvariantIsing.Magnetic.RestrictedRotationArray
import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalSpinObservable
import OAI.Probability.InvariantIsing.Cavity.CavitySpinSplitOverlap
import OAI.Probability.InvariantIsing.Cavity.CavityRotationVectors

namespace OAI

/-! Actual eigenbasis/Gaussian disorder and the ordinary spin overlap
specialize the finite-cavity scalar-field identity. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem restricted_physical_overlap_cutoff (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m q dim kspin : ℕ} (N depth : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (S : (n : ℕ) → Finset (Spin (N n))) (hS : ∀ n, (S n).Nonempty)
    (dims : ℕ → Fin m → ℕ) (hgroups : ∀ n a, 0 < dims n a)
    (hdims : ∀ a, Tendsto (fun n => dims n a) atTop atTop)
    (E : (n : ℕ) → ((a : Fin m) × Fin (dims n a)) ≃ Fin (N n))
    (μ : (n : ℕ) → Measure (Orthogonal (N n))) [∀ n, IsProbabilityMeasure (μ n)]
    (θ : (n : ℕ) → Measure (LabeledTree (depth n))) [∀ n, IsProbabilityMeasure (θ n)]
    (μG : (n : ℕ) → (a : Fin m) → Measure (Orthogonal (dims n a)))
    [∀ n a, IsProbabilityMeasure (μG n a)] [∀ n a, (μG n a).IsMulRightInvariant]
    (A₀ : (n : ℕ) → (a : Fin m) → Matrix (Fin (dims n a)) (Fin q) ℝ)
    (hA₀ : ∀ n a, (A₀ n a).transpose * A₀ n a = 1)
    (eigN : (n : ℕ) → Fin (N n) → ℝ) (u : ℕ → ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) (hcG : ∀ n a, c ≤ (dims n a : ℝ)/N n)
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρlim : Tendsto (fun n a => (dims n a : ℝ)/N n) atTop (𝓝 ρ))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun n => restrictedRotationArrayLaw (S n) (hS n) (μ n) (θ n) (eigN n)
      (cavitySpectralGroup (fun i => ((E n).symm i).1)) (u n)) atTop (𝓝 Q₀))
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
    (hdim : 0 < dim) (hkspin : 0 < kspin)
    (T : Finset (Spin kspin)) (hT : T.Nonempty)
    (B₀ : Matrix (Fin (m*kspin)) (Fin dim) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (hBE : B₀.transpose * cavityLimitingStack (n := kspin) ρ = 0)
    (hcomplete : B₀ * B₀.transpose + cavityLimitingStack (n := kspin) ρ *
      (cavityLimitingStack (n := kspin) ρ).transpose = 1)
    (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {M : ℝ} (hΦb : ∀ x, |Φ x| ≤ M)
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop)
    (hnull : ∀ j s, (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m s) : Measure
      (SpectralBlock m s × EuclideanSpace ℝ (Fin m × (Fin s × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let K := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig * B₀ -
      Matrix.diagonal (fun i => eig (g i))
    let L := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig *
      cavityLimitingStack (n := kspin) ρ
    let Cspin := (finiteR ρ eig hρ hρsum 0) • (1 : Matrix (Fin kspin) (Fin kspin) ℝ)
    let τ := fun j => cavityFactorSize K L Cspin * (1+(b j)^2)
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      |(∫ ω, cavityWeightedReplicaMean
          ((restrictedRotationProbability (S n) (hS n) (eigN n)
            (cavitySpectralGroup (fun i => ((E n).symm i).1)) (u n) ω.1).prod
            (restrictedSpinPrior T hT))
          (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors (dims n) (E n))
            (A₀ n) K L Cspin (τ j) (b j) (ω,x))
          (fun σ : Fin 2 → (Spin (N n) × LabeledLeaf (depth n)) × Spin kspin =>
            Φ (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1)))
          ∂(((μ n).prod (θ n)).prod gaussianCoordinates).prod (Measure.pi (μG n))) -
        ∫ t, Φ (cavityStrictUniformPath p n t) ∂pathMeasure| < ε := by
  intro p K L Cspin τ
  let I n := cavitySpectralGroup (fun i => ((E n).symm i).1)
  let Ω n := (Orthogonal (N n) × LabeledTree (depth n)) × (ℕ → ℝ)
  let X n := Spin (N n) × LabeledLeaf (depth n)
  let P n := ((μ n).prod (θ n)).prod gaussianCoordinates
  let ν n := restrictedRotationProbability (S n) (hS n) (depth := depth n) (eigN n) (I n) (u n)
  let B n := cavityRotationEntry (depth := depth n) (I n)
  let Q n := restrictedRotationArrayLaw (S n) (hS n) (μ n) (θ n) (eigN n) (I n) (u n)
  have hρs n a : 0 < (dims n a : ℝ)/N n :=
    div_pos (Nat.cast_pos.mpr (hgroups n a)) (Nat.cast_pos.mpr (hN n))
  have hh := restricted_haar_finite_overlap_cutoff hpub dims hdims μG A₀ hA₀ Ω X P ν
    (fun n => measurable_restrictedRotationProbability _ _ _ _ _) B
    (fun n => measurable_cavityRotationEntry (I n))
    (fun n => cavityRotationEntry_gram (I n))
    (fun n => cavityRotationVectors (dims n) (E n))
    (fun n => measurable_cavityRotationVectors (dims n) (E n)) (1/c)
    (fun s n x => cavityRotationVectors_gram_bound (r := s) (hN n) (dims n) (E n) x hc (hcG n))
    (fun n a => (dims n a : ℝ)/N n) ρ eig hρs hρ hρlim hρsum
    (fun s n x => cavityRotationVectors_covariance (r := s) (hN n) (dims n) (E n) x q)
    Q Q₀ (fun _ => rfl) hlim hgg hG d hd0 hd hE hP hn hoff hdiag g e he heg
    hgroups (div_nonneg zero_le_one hc.le) hdim hkspin T hT B₀ hB₀ hBE hcomplete a ha Φ hΦ hΦb
    b hb hblim hnull
  dsimp only at hh
  intro ε hε
  filter_upwards [hh ε hε] with j hj
  filter_upwards [hj] with n hn'
  have htest (ω : Ω n × ((a : Fin m) → Orthogonal (dims n a))) : cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1)
      (cavityOverlapObservable Φ hΦ) =
      (fun σ : Fin 2 → (Spin (N n) × LabeledLeaf (depth n)) × Spin kspin =>
            Φ (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1))) := by
    funext σ
    exact cavity_physical_overlap_observable (fun i => ((E n).symm i).1) ω.1 Φ hΦ σ
  simpa only [htest] using hn'

end InvariantIsing

end

end OAI
