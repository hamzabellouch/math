import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateQuadraticExpansion

namespace OAI

/-! Exact full quadratic expansion: the metric and polynomial remainders
share one finite family of doubled and mixed nonzero phases. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

def combinedQuadraticMean {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ) :
    SmallModes.Base → PhaseMean.Tensor :=
  RealModes.zeroPhaseSum τ (fun i => coordinatePhase (φ i))
    (fun i => coordinateAmplitude (H i)) + coordinateQuadraticMean P ε G φ H τ t

def combinedQuadraticCoefficient {n : ℕ} {ι : Type*}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ)
    (l : RealModes.QuadraticLabel ι) : SmallModes.Tensor :=
  RealModes.quadraticAmplitude τ (fun i => coordinatePhase (φ i))
    (fun i => coordinateAmplitude (H i)) l + coordinateQuadraticCoefficient P ε G φ H τ t l

lemma displacement_add (τ : ℝ) (φ : SmallModes.Base → ℝ) (A B : SmallModes.Tensor) :
    QuadraticMean.displacement τ φ (A + B) =
      QuadraticMean.displacement τ φ A + QuadraticMean.displacement τ φ B := by
  funext p i
  simp only [QuadraticMean.displacement, QuadraticMean.realMode, QuadraticMean.realPart,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Complex.add_re]

theorem combined_quadratic_expansion {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hH : ∀ i, ContDiff ℝ ∞ (H i)) (τ t : ℝ) :
    let X := QuadraticMean.sumDisplacement τ (fun i => coordinatePhase (φ i))
      (fun i => coordinateAmplitude (H i))
    RealModes.realMetricTensor X + coordinateQuadraticPolynomial P ε G X t =
      combinedQuadraticMean P ε G φ H τ t +
        fun p => ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ
            (RealModes.quadraticPhase (fun i => coordinatePhase (φ i)) l)
            (combinedQuadraticCoefficient P ε G φ H τ t l) p := by
  dsimp only
  have hp := coordinate_quadratic_polynomial_expansion P ε G φ H hφ hH τ t
  dsimp only at hp
  rw [hp]
  funext p
  have hm := RealModes.realMetric_sumDisplacement
    (fun i => ((hφ i).comp planeCoordinateIsometry.symm.contDiff).differentiable (by simp) p)
    (fun i => ((hH i).comp planeCoordinateIsometry.symm.contDiff).differentiable (by simp) p) τ
  change RealModes.realMetricTensor _ p + _ = _
  rw [hm, RealModes.nonzeroPhaseSum_eq_quadraticFamily]
  simp only [combinedQuadraticMean, combinedQuadraticCoefficient, displacement_add,
    Pi.add_apply, Finset.sum_add_distrib]
  abel

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
