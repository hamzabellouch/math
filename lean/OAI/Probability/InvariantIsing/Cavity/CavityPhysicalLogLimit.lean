import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalSpinCutoff
import OAI.Probability.InvariantIsing.Cavity.CavityHaarGibbsCappedLog

namespace OAI

/-! Capped logarithmic convergence with the actual base-system Gibbs
kernel and physical spectral-group coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_physical_capped_log_limit
    {m q dim kspin : ℕ} (N depth : ℕ → ℕ) (hN : ∀ n, 0 < N n)
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
    (hlim : Tendsto (fun n => cavityRotationArrayLaw (μ n) (θ n) (eigN n)
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
    (K : Matrix (Fin dim) (Fin dim) ℝ) (L : Matrix (Fin dim) (Fin kspin) ℝ)
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ) (T : ℝ) (hT : 0 ≤ T) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let Qf := fun r => cavityLabeledDisorderLaw r (chainExponent (uniformCut r))
      (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p r)
        (cavityStrictUniformLevels p r))
      (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p r)
        (uniformCut r) (cavityStrictUniformLevels p r))
    let η := fun r => cavityLabeledPriorKernel r
      (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p r)
        (cavityStrictUniformLevels p r) r) (uniformSpinPrior kspin)
    Tendsto (fun r =>
      (∫ ω, Real.log (∫ x, Real.exp (min
        (cavityHaarSpinPotential e (cavityRotationVectors (dims r) (E r)) (A₀ r) K L Cspin (ω,x)) T)
        ∂((cavityRotationProbability (eigN r)
          (cavitySpectralGroup (fun i => ((E r).symm i).1)) (u r) ω.1).prod (uniformSpinPrior kspin)))
        ∂(((μ r).prod (θ r)).prod gaussianCoordinates).prod (Measure.pi (μG r))) -
      ∫ ω, Real.log (∫ x, Real.exp (min (cavityLabeledPotential r K L Cspin (ω,x)) T)
        ∂η r ω) ∂Qf r) atTop (𝓝 0) := by
  intro p Qf η
  let I r := cavitySpectralGroup (fun i => ((E r).symm i).1)
  let Ω r := (Orthogonal (N r) × LabeledTree (depth r)) × (ℕ → ℝ)
  let X r := Spin (N r) × LabeledLeaf (depth r)
  let P r := ((μ r).prod (θ r)).prod gaussianCoordinates
  let ν r := cavityRotationProbability (depth := depth r) (eigN r) (I r) (u r)
  let B r := cavityRotationEntry (depth := depth r) (I r)
  let Q r := cavityRotationArrayLaw (μ r) (θ r) (eigN r) (I r) (u r)
  have hρs r a : 0 < (dims r a : ℝ)/N r :=
    div_pos (Nat.cast_pos.mpr (hgroups r a)) (Nat.cast_pos.mpr (hN r))
  exact cavity_haar_gibbs_capped_log_match dims hdims hgroups μG A₀ hA₀ Ω X P ν
    (fun r => measurable_cavityRotationProbability _ _ _) B
    (fun r => measurable_cavityRotationEntry (I r))
    (fun r => cavityRotationEntry_gram (I r))
    (fun r => cavityRotationVectors (dims r) (E r))
    (fun r => measurable_cavityRotationVectors (dims r) (E r)) (1/c)
    (div_nonneg zero_le_one hc.le)
    (fun s r x => cavityRotationVectors_gram_bound (r := s) (hN r) (dims r) (E r) x hc (hcG r))
    (fun r a => (dims r a : ℝ)/N r) ρ eig hρs hρ hρlim hρsum
    (fun s r x => cavityRotationVectors_covariance (r := s) (hN r) (dims r) (E r) x q)
    Q Q₀ (fun _ => rfl) hlim hgg hG d hd0 hd hE hP hn hoff hdiag g e he heg
    K L Cspin T hT (uniformSpinPrior kspin)

end InvariantIsing

end

end OAI
