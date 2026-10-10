import OAI.Geometry.SurfaceImmersion.Correction.ChartedFreeMetricSplit

namespace OAI

/-! At zero perturbation the actual quadratic mean is its metric zero phase. -/
noncomputable section
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean
namespace ChartedMeanFamilyData

lemma quadraticMean_unperturbed {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {τ : ℝ} {s : ℝ≥0} {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanFamilyData P 0 τ s r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (f : SmallModes.Base → Tensor) :
    d.quadraticMean hρ δ q f = RealModes.zeroPhaseSum τ
      (fun j => coordinatePhase (d.phase j))
      (fun j => coordinateAmplitude ((d.data j).freeAmplitude hρ δ q f)) := by
  ext x k
  simp [quadraticMean,combinedQuadraticMean,coordinateQuadraticMean,
    quadraticMeanCoefficient,conjugated]

end ChartedMeanFamilyData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
