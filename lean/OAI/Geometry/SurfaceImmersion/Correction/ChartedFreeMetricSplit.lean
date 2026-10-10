import OAI.Geometry.SurfaceImmersion.Correction.ChartedFreeFamily
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanFamilyData
import OAI.Geometry.SurfaceImmersion.Correction.FreeForcedIncrementIdentity

namespace OAI

/-! Exact mean/oscillation split of the metric of the actual free family
when the polynomial perturbation parameter is zero. -/
noncomputable section
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes
namespace ChartedMeanFamilyData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ} {s : ℝ≥0}
  {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

def quadraticOscillation (d : ChartedMeanFamilyData P ε τ s r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (f : SmallModes.Base → Tensor) : SmallModes.Base → Tensor :=
  combinedNonzeroQuadratic P ε d.G d.phase
    (fun j => (d.data j).freeAmplitude hρ δ q f) τ

lemma free_metric_split (d : ChartedMeanFamilyData P 0 τ s r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (f : SmallModes.Base → Tensor) :
    realMetricTensor (chartedFreeSum d.data hρ δ q f) =
      d.quadraticMean hρ δ q f + d.quadraticOscillation hρ δ q f := by
  have he := combined_quadratic_expansion P 0 d.G d.phase
    (fun j => (d.data j).freeAmplitude hρ δ q f)
    (fun j => (d.solver j).smoothPhase)
    (fun j => ((d.data j).freeAmplitude hρ δ q f).contDiff) τ 0
  dsimp only at he
  have hz : coordinateQuadraticPolynomial P 0 d.G
      (chartedFreeSum d.data hρ δ q f) 0 = 0 := by
    ext x k
    simp [coordinateQuadraticPolynomial]
  change realMetricTensor (chartedFreeSum d.data hρ δ q f) +
    coordinateQuadraticPolynomial P 0 d.G (chartedFreeSum d.data hρ δ q f) 0 = _ at he
  rw [hz,add_zero] at he
  exact he

end ChartedMeanFamilyData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
