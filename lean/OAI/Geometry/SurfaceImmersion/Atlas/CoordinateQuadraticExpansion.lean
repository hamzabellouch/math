import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadraticFamily
import OAI.Geometry.SurfaceImmersion.Correction.CoordinateLinearizedResidual

namespace OAI

/-! Transport the polynomial quadratic expansion into the same coordinates
and phase labels as the metric quadratic expansion. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open MixedExpression ModulatedJets

abbrev coordinatePhase (φ : Base → ℝ) : SmallModes.Base → ℝ := φ ∘ planeCoordinateIsometry.symm
abbrev coordinateAmplitude (H : Base → Fin 4 → ℂ) : SmallModes.Field 4 := H ∘ planeCoordinateIsometry.symm

lemma coordinate_phase_value (τ : ℝ) (φ : Base → ℝ) (x : Base) :
    QuadraticMean.phase (φ x / τ) = phase τ φ x := by
  simp only [QuadraticMean.phase, phase, Complex.ofReal_div]
  congr 1
  ring

lemma real_oscillatorySum_coordinates {ι : Type*} [Fintype ι]
    (τ : ℝ) (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) :
    realField (oscillatorySum τ φ H) =
      QuadraticMean.sumDisplacement τ (fun i => coordinatePhase (φ i))
        (fun i => coordinateAmplitude (H i)) ∘ planeCoordinateIsometry := by
  funext x a
  simp only [realField, oscillatorySum, Finset.sum_apply, Complex.re_sum,
    QuadraticMean.sumDisplacement, Function.comp_apply, QuadraticMean.displacement,
    QuadraticMean.realMode, QuadraticMean.realPart, coordinatePhase, coordinateAmplitude,
    planeCoordinateIsometry.symm_apply_apply, Pi.smul_apply, smul_eq_mul, coordinate_phase_value]

lemma coordinate_quadratic_phase {ι : Type*} (φ : ι → Base → ℝ)
    (l : RealModes.QuadraticLabel ι) (x : SmallModes.Base) :
    quadraticFamilyPhase φ l (planeCoordinateIsometry.symm x) =
      RealModes.quadraticPhase (fun i => coordinatePhase (φ i)) l x := by
  rcases l with i | ⟨i,j,b⟩
  · rfl
  · cases b <;> rfl

def coordinateQuadraticPolynomial {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (X : RealModes.RField 4) (t : ℝ) : SmallModes.Base → Fin 3 → ℝ :=
  fun p k => ∑ l, ε ^ (l.val + 1) * ((1 / 2 : ℝ) * ((P k l).variations 1).eval
    ![G, X ∘ planeCoordinateIsometry, X ∘ planeCoordinateIsometry, 0] (planeCoordinateIsometry.symm p,t))

def coordinateQuadraticMean {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ) :
    SmallModes.Base → Fin 3 → ℝ :=
  fun p k => ∑ i, quadraticMeanCoefficient (P k) ε G (φ i) (H i) τ t (planeCoordinateIsometry.symm p)

def coordinateQuadraticCoefficient {n : ℕ} {ι : Type*}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ)
    (l : RealModes.QuadraticLabel ι) : SmallModes.Tensor :=
  fun p k => quadraticFamilyCoefficient (P k) ε G φ H τ t l (planeCoordinateIsometry.symm p)

theorem coordinate_quadratic_polynomial_expansion {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hH : ∀ i, ContDiff ℝ ∞ (H i)) (τ t : ℝ) :
    let X := QuadraticMean.sumDisplacement τ (fun i => coordinatePhase (φ i))
      (fun i => coordinateAmplitude (H i))
    coordinateQuadraticPolynomial P ε G X t =
      coordinateQuadraticMean P ε G φ H τ t +
        fun p => ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ
            (RealModes.quadraticPhase (fun i => coordinatePhase (φ i)) l)
            (coordinateQuadraticCoefficient P ε G φ H τ t l) p := by
  dsimp only
  funext p k
  unfold coordinateQuadraticPolynomial
  rw [← real_oscillatorySum_coordinates τ φ H]
  rw [quadratic_zero_phase_expansion (P k) ε G φ H hφ hH τ t (planeCoordinateIsometry.symm p),
    quadraticOscillation_eq_family]
  simp only [Pi.add_apply, Finset.sum_apply, coordinateQuadraticMean]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  simp only [QuadraticMean.displacement, QuadraticMean.realMode, QuadraticMean.realPart,
    Pi.smul_apply, smul_eq_mul, coordinateQuadraticCoefficient]
  rw [← coordinate_quadratic_phase φ l p]
  exact congrArg Complex.re (congrArg (fun z : ℂ => z *
    quadraticFamilyCoefficient (P k) ε G φ H τ t l (planeCoordinateIsometry.symm p))
      (coordinate_phase_value τ (quadraticFamilyPhase φ l) (planeCoordinateIsometry.symm p))).symm

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
