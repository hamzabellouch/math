import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanData
import OAI.Geometry.SurfaceImmersion.Correction.FiniteMeanFamily

namespace OAI

/-! Assemble the actual charted free amplitudes and their zero-phase tensors. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean
variable {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
    {K : ι → Compacts Base} {s : ℝ≥0}
    {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanData (c i) r ρ R reference)

def chartedFamilyMean (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    SmallModes.Base → Tensor := fun x => ∑ i, (d i).mean hρ δ q A x

def chartedFamilyLeading (hρ : 0 < ρ) (A : SmallModes.Base → Tensor) :
    SmallModes.Base → Tensor := fun x => ∑ i, (d i).leading hρ A x

theorem charted_family_zero_phase_identity (hρ : 0 < ρ) {δ : ℝ}
    (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ) (A : SmallModes.Base → Tensor) :
    combinedQuadraticMean P ε G φ (fun i => (d i).freeAmplitude hρ δ q A) τ 0 =
      δ ^ 2 • (chartedFamilyLeading d hρ A + chartedFamilyMean d hρ δ q A) := by
  funext x k
  simp only [combinedQuadraticMean, zeroPhaseSum, coordinateQuadraticMean, Pi.add_apply,
    Finset.sum_apply]
  change (∑ i, phaseZeroTensor τ (coordinatePhase (φ i))
      (coordinateAmplitude ((d i).freeAmplitude hρ δ q A)) x k) +
      (∑ i, quadraticMeanCoefficient (P k) ε G (φ i) ((d i).freeAmplitude hρ δ q A) τ 0
        (planeCoordinateIsometry.symm x)) = _
  rw [← Finset.sum_add_distrib]
  simp_rw [show ∀ i, phaseZeroTensor τ (coordinatePhase (φ i))
      (coordinateAmplitude ((d i).freeAmplitude hρ δ q A)) x k +
      quadraticMeanCoefficient (P k) ε G (φ i) ((d i).freeAmplitude hρ δ q A) τ 0
        (planeCoordinateIsometry.symm x) =
      δ ^ 2 * ((d i).leading hρ A x k + (d i).mean hρ δ q A x k) from
    fun i => congrFun ((d i).zero_phase_identity hρ hδ hτ q A x) k]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Pi.smul_apply, smul_eq_mul,
    Pi.add_apply, chartedFamilyLeading, chartedFamilyMean, Finset.sum_apply, mul_add]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
