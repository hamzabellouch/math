import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternPublishedInputs
import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternZeroOrbit
import OAI.Probability.InvariantIsing.Fields.CanonicalOrthogonalLaw

namespace OAI

/-! The Gaussian-pattern pressure limit from Haar concentration, cascade
identities, Marchenko–Pastur convergence, and spectral edge estimates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
universe u
namespace InvariantIsing

def gaussianPatternLimit (α c : ℝ) : ℝ :=
  (variationalFunctional (measureR
    ((marchenkoPasturMeasure α).map (fun x => c*x))
    (max (c*marchenkoPasturLower α) (c*marchenkoPasturB α)))).toReal

theorem gaussianPattern_pressure_uniformIntegrable
    (α : ℝ) (hα : 0 < α) (hmp : MarchenkoPasturInput.{u} α hα)
    (hds : DavidsonSzarekInput.{u} α hα)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, Measurable (Z N)) (hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P)
    (c : ℝ) : UniformIntegrable (fun k ω => gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω)) 1 P := by
  let : ∀ N, IsProbabilityMeasure (orthogonalGaussianHaar N) :=
    fun N => orthogonalGaussianHaar_probability N
  let : ∀ N, (orthogonalGaussianHaar N).IsMulRightInvariant :=
    fun N => orthogonalGaussianHaar_rightInvariant N
  let eig := fun (N : ℕ) (ω : Ω) (i : Fin N) => c*gaussianPatternEigenvalues (N := N) (m := gaussianPatternCount α N) (Z N ω) i
  let Y := fun (N : ℕ) (ω : Ω) => gaussianPatternPressure (N := N) (m := gaussianPatternCount α N) c (Z N ω)
  have heig (N : ℕ) : Measurable (eig N) := by
    exact measurable_pi_iff.mpr fun i =>
      (((measurable_pi_apply i).comp (hmp.measurable_eigenvalues N)).comp (hZ N)).const_mul c
  have hY (N : ℕ) : Measurable (Y N) :=
    (measurable_gaussianPatternPressure N _ c).comp (hZ N)
  have horbit (N : ℕ) : ConditionalFieldOrbitLaw P
      (fun ω => (eig N ω,fun _ => 0)) (Y N) (orthogonalGaussianHaar N) := by
    exact gaussianPattern_conditionalOrbit_all c P (Z N) (hZ N) (hlaw N)
      (hmp.measurable_eigenvalues N) _
  have hspec := hds.uniform_integrable P Z hlaw c
  change UniformIntegrable (fun k ω => spectralRadius (eig (k+1) ω)) 1 P at hspec
  change UniformIntegrable (fun k => Y (k+1)) 1 P
  exact random_pressure_uniformIntegrable_of_spectralRadius P eig Y heig hY
    orthogonalGaussianHaar horbit hspec

theorem gaussianPattern_pressure_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (α : ℝ) (hα : 0 < α) (hmp : MarchenkoPasturInput.{u} α hα)
    (hds : DavidsonSzarekInput.{u} α hα)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, Measurable (Z N)) (hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P)
    (c : ℝ) :
    TendstoInMeasure P (fun k ω => gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω)) atTop
      (fun _ => gaussianPatternLimit α c) ∧
    Tendsto (fun k => eLpNorm (fun ω => gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω)-
      gaussianPatternLimit α c) 1 P) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ ω, gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω) ∂P) atTop
      (𝓝 (gaussianPatternLimit α c)) := by
  let : ∀ N, IsProbabilityMeasure (orthogonalGaussianHaar N) :=
    fun N => orthogonalGaussianHaar_probability N
  let : ∀ N, (orthogonalGaussianHaar N).IsMulRightInvariant :=
    fun N => orthogonalGaussianHaar_rightInvariant N
  let eig := fun (N : ℕ) (ω : Ω) (i : Fin N) => c*gaussianPatternEigenvalues (N := N) (m := gaussianPatternCount α N) (Z N ω) i
  let Y := fun (N : ℕ) (ω : Ω) => gaussianPatternPressure (N := N) (m := gaussianPatternCount α N) c (Z N ω)
  have heig (N : ℕ) : Measurable (eig N) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (((measurable_pi_apply i).comp (hmp.measurable_eigenvalues N)).comp (hZ N)).const_mul c
  have hY (N : ℕ) : Measurable (Y N) :=
    (measurable_gaussianPatternPressure N _ c).comp (hZ N)
  have horbit (N : ℕ) : ConditionalFieldOrbitLaw P
      (fun ω => (eig N ω,fun _ => 0)) (Y N) (orthogonalGaussianHaar N) := by
    exact gaussianPattern_conditionalOrbit_all c P (Z N) (hZ N) (hlaw N)
      (hmp.measurable_eigenvalues N) _
  let ν : ProbabilityMeasure ℝ := ⟨marchenkoPasturMeasure α,hmp.probability⟩
  let a := min (c*marchenkoPasturLower α) (c*marchenkoPasturB α)
  let b := max (c*marchenkoPasturLower α) (c*marchenkoPasturB α)
  have hbound : (scaledSpectralLaw ν c : Measure ℝ).support ⊆ Icc a b :=
    signed_scaled_spectral_support ν _ _ c hmp.support_bound
  have hends := signed_scaled_spectral_endpoints ν _ _ c hmp.left_mem hmp.right_mem
  have hcompact : IsCompact (scaledSpectralLaw ν c : Measure ℝ).support :=
    isCompact_Icc.of_isClosed_subset Measure.isClosed_support hbound
  have hspec := hds.uniform_integrable P Z hlaw c
  change UniformIntegrable (fun k ω => spectralRadius (eig (k+1) ω)) 1 P at hspec
  have hUI : UniformIntegrable (fun k => Y (k+1)) 1 P :=
    random_pressure_uniformIntegrable_of_spectralRadius P eig Y heig hY
      orthogonalGaussianHaar horbit hspec
  exact random_pressure_limit hhaar hgauss hpub P eig Y heig hY orthogonalGaussianHaar
    horbit (scaledSpectralLaw ν c) a b hcompact hbound hends.1 hends.2
    (hmp.weak P Z hlaw c) (hds.excess P Z hlaw c) hUI

end InvariantIsing

end

end OAI
