import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternPressureLimit
import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternGroundFinite
import OAI.Probability.InvariantIsing.Pressure.RandomGroundLimit

namespace OAI

/-! Subsequent zero-temperature limits for both signs of the Gaussian energy. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
universe u
namespace InvariantIsing

lemma gaussianPattern_ground_uniformIntegrable
    (α : ℝ) (hα : 0 < α) (hds : DavidsonSzarekInput.{u} α hα)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, Measurable (Z N)) (hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P)
    (ε : ℝ) : UniformIntegrable (fun k ω => gaussianPatternGroundEnergy ε (Z (k+1) ω)) 1 P := by
  apply uniformIntegrable_of_abs_le P _ _
    (fun k => ((measurable_gaussianPatternGroundEnergy _ _ ε).comp (hZ (k+1))).aestronglyMeasurable)
    (hds.uniform_integrable P Z hlaw ε)
  intro k
  filter_upwards [] with ω
  have hr : 0 ≤ spectralRadius (fun i => ε*gaussianPatternEigenvalues (Z (k+1) ω) i) :=
    (abs_nonneg (ε*gaussianPatternEigenvalues (Z (k+1) ω) 0)).trans (abs_le_spectralRadius (fun i => ε*gaussianPatternEigenvalues (Z (k+1) ω) i) 0)
  exact (abs_gaussianPatternGroundEnergy_le ε _).trans ((half_le_self hr).trans (le_abs_self _))

theorem gaussianPattern_ground_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (α : ℝ) (hα : 0 < α) (hmp : MarchenkoPasturInput.{u} α hα)
    (hds : DavidsonSzarekInput.{u} α hα)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, Measurable (Z N)) (hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P)
    (ε : ℝ) :
    ∃ e : ℝ,
      TendstoInMeasure P (fun k ω => gaussianPatternGroundEnergy ε (Z (k+1) ω)) atTop (fun _ => e) ∧
      Tendsto (fun k => eLpNorm (fun ω => gaussianPatternGroundEnergy ε (Z (k+1) ω)-e) 1 P)
        atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ ω, gaussianPatternGroundEnergy ε (Z (k+1) ω) ∂P) atTop (𝓝 e) ∧
      Tendsto (fun β => gaussianPatternLimit α (ε*β)/β) atTop (𝓝 e) := by
  apply random_ground_limit P
    (fun β k ω => gaussianPatternPressure (ε*β) (Z (k+1) ω))
    (fun k ω => gaussianPatternGroundEnergy ε (Z (k+1) ω))
    (fun β => gaussianPatternLimit α (ε*β)) (Real.log 2)
    (Real.log_pos (by norm_num : (1 : ℝ)<2)).le
    (gaussianPattern_ground_uniformIntegrable α hα hds P Z hZ hlaw ε)
  · intro β k
    exact (measurable_gaussianPatternPressure _ _ _).comp (hZ (k+1))
  · intro β _ k
    exact memLp_one_iff_integrable.mp
      ((gaussianPattern_pressure_uniformIntegrable α hα hmp hds P Z hZ hlaw (ε*β)).memLp k)
  · intro β _
    exact (gaussianPattern_pressure_limit hhaar hgauss hpub α hα hmp hds P Z hZ hlaw (ε*β)).1
  · intro β _
    exact (gaussianPattern_pressure_limit hhaar hgauss hpub α hα hmp hds P Z hZ hlaw (ε*β)).2.2
  · intro β hβ k ω
    exact gaussianPatternGroundEnergy_squeeze (Nat.succ_pos k) ε β hβ _

end InvariantIsing

end

end OAI
