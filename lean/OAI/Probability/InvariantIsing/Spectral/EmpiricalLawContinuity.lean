import OAI.Probability.InvariantIsing.Gaussian.GaussianEmpiricalWeak

namespace OAI

/-! Continuity of finite empirical spectral measures in their actual eigenvalues. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace InvariantIsing

theorem continuous_empiricalSpectralLaw {N : ℕ} (hN : 0 < N) :
    Continuous (fun eig : Fin N → ℝ => empiricalSpectralLaw hN eig) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  simp only [empiricalSpectralLaw_integral]
  exact continuous_const.mul (continuous_finsetSum _ fun i _ => f.continuous.comp (continuous_apply i))

theorem continuous_scaled_gaussianEmpirical {N m : ℕ} (hN : 0 < N) (c : ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin m) => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw hN (fun i => c*gaussianPatternEigenvalues z i))) := by
  apply LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp
  apply (continuous_empiricalSpectralLaw hN).comp
  apply continuous_pi
  intro i
  exact continuous_const.mul ((continuous_apply i).comp (continuous_gaussianPatternEigenvalues N m))

end InvariantIsing

end

end OAI
