import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternOrbitLaw
import OAI.Probability.InvariantIsing.Spectral.ScaledSpectralSigned
import OAI.Probability.InvariantIsing.Pressure.RandomPressureMain

namespace OAI

/-! Marchenko–Pastur and Davidson–Szarek estimates for Gaussian-pattern matrices.
MP1967, Theorem1 and examples pp.459,461, gives the displayed law and empirical
limit. DS2001, TheoremII.13, gives the edge-excess and uniform-integrability
consequences for the Gaussian rectangular matrix. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
universe u
namespace InvariantIsing

@[irreducible] def gaussianPatternCount (α : ℝ) (N : ℕ) : ℕ := ⌊α*N⌋₊
def marchenkoPasturA (α : ℝ) : ℝ := (1-Real.sqrt α)^2
def marchenkoPasturB (α : ℝ) : ℝ := (1+Real.sqrt α)^2
def marchenkoPasturLower (α : ℝ) : ℝ := if α ≤ 1 then 0 else marchenkoPasturA α

def marchenkoPasturMeasure (α : ℝ) : Measure ℝ :=
  ENNReal.ofReal (max (1-α) 0) • Measure.dirac 0 +
    volume.withDensity ((Icc (marchenkoPasturA α) (marchenkoPasturB α)).indicator
      (fun x => ENNReal.ofReal
        (Real.sqrt ((marchenkoPasturB α-x)*(x-marchenkoPasturA α))/(2*Real.pi*x))))

/-- The fixed-aspect-ratio Gaussian specialization of MP1967, Theorem1. -/
structure MarchenkoPasturInput (α : ℝ) (_hα : 0 < α) : Prop where
  probability : IsProbabilityMeasure (marchenkoPasturMeasure α)
  support_bound : (marchenkoPasturMeasure α).support ⊆ Icc (marchenkoPasturLower α) (marchenkoPasturB α)
  left_mem : marchenkoPasturLower α∈(marchenkoPasturMeasure α).support
  right_mem : marchenkoPasturB α∈(marchenkoPasturMeasure α).support
  measurable_eigenvalues : ∀ N, Measurable
    (gaussianPatternEigenvalues (N := N) (m := gaussianPatternCount α N))
  weak : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N))),
    (∀ N, HasLaw (Z N) (stdGaussian _) P) → ∀ c : ℝ,
    TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k)
        (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i))) atTop
      (fun _ => LevyProkhorov.ofMeasure
        (scaledSpectralLaw ⟨marchenkoPasturMeasure α,probability⟩ c))

/-- The edge and integrable-tail consequences of DS2001, TheoremII.13.
The rank-deficient case uses the exact zero eigenvalues of the Gram matrix. -/
structure DavidsonSzarekInput (α : ℝ) (_hα : 0 < α) : Prop where
  excess : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N))),
    (∀ N, HasLaw (Z N) (stdGaussian _) P) → ∀ c : ℝ,
    TendstoInMeasure P (fun k ω => spectralExcess
      (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i)
      (min (c*marchenkoPasturLower α) (c*marchenkoPasturB α))
      (max (c*marchenkoPasturLower α) (c*marchenkoPasturB α))) atTop (fun _ => 0)
  uniform_integrable : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N))),
    (∀ N, HasLaw (Z N) (stdGaussian _) P) → ∀ c : ℝ,
    UniformIntegrable (fun k ω => spectralRadius
      (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i)) 1 P

end InvariantIsing

end

end OAI
