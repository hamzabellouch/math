import OAI.Probability.InvariantIsing.Fields.SpinPriorCascadePressure
import OAI.Probability.InvariantIsing.Fields.PriorFieldDerivative

namespace OAI

/-! The quenched cascade pressure is exactly the average of the fixed-leaf
prior pressures. The logarithm remains inside the cascade average. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

lemma spinPriorMeanPressure_prior_average
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m k n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    Integrable (fun T => priorNamespacedMeanPressure μ (labeledSpinReference n π T)
      eig c I degree amp r h) (labeledCascadeLaw n b : Measure (LabeledTree n)) ∧
    spinPriorMeanPressure (n := n) μ π eig c I degree amp b r h =
      ∫ T, priorNamespacedMeanPressure μ (labeledSpinReference n π T) eig c I degree amp r h
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  let τ := (labeledCascadeLaw n b : Measure (LabeledTree n))
  let F := spinPriorNamespacedLog (n := n) π eig c I degree amp r h
  let G := fun q : SpecialOrthogonal N × LabeledTree n => ∫ z, F (q,z) ∂gaussianCoordinates
  have hF : Integrable F ((μ.prod τ).prod gaussianCoordinates) :=
    spinPriorNamespacedLog_integrable μ π eig c I degree amp b r h hh h0
  have hG : Integrable G (μ.prod τ) := hF.integral_prod_left
  have he T : (∫ U, G (U,T) ∂μ) =
      ∫ p, priorNamespacedLog (labeledSpinReference n π T) eig c I degree amp
        (fun i => tensorPathProfile I degree n r h i) p ∂μ.prod gaussianCoordinates := by
    exact (integral_prod _ (priorNamespacedLog_integrable hhaar hgauss hN μ hμ
      (labeledSpinReference n π T) eig c I degree amp (fun i => varianceIncrement h i)
      (fun i j => varianceIncrement (monomialPath n (r j)) i))).symm
  have hraw : (∫ p, F p ∂(μ.prod τ).prod gaussianCoordinates) =
      ∫ T, ∫ p, priorNamespacedLog (labeledSpinReference n π T) eig c I degree amp
        (fun i => tensorPathProfile I degree n r h i) p ∂μ.prod gaussianCoordinates ∂τ := by
    rw [integral_prod _ hF]
    change (∫ q, G q ∂μ.prod τ) = _
    rw [integral_prod _ hG, integral_integral_swap hG]
    simp_rw [he]
  have hi : Integrable (fun T => ∫ p, priorNamespacedLog (labeledSpinReference n π T)
      eig c I degree amp (fun i => tensorPathProfile I degree n r h i) p
      ∂μ.prod gaussianCoordinates) τ := by
    exact hG.swap.integral_prod_left.congr (ae_of_all _ he)
  refine ⟨(hi.const_mul (N : ℝ)⁻¹).sub (integrable_const _),?_⟩
  unfold spinPriorMeanPressure priorNamespacedMeanPressure
  change (N : ℝ)⁻¹*(∫ p, F p ∂(μ.prod τ).prod gaussianCoordinates)-h n/2 = _
  rw [hraw, integral_sub (hi.const_mul _) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul]

lemma spinPriorNamespacedLog_uniform {N m k n : ℕ}
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (p : TensorFlatDisorder N n) :
    spinPriorNamespacedLog (uniformSpinPrior N : Measure (Spin N)) eig c I degree amp r h p =
      tensorNamespacedLog eig c I degree amp n r h p := rfl

lemma spinPriorMeanPressure_uniform {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    spinPriorMeanPressure (n := n) μ (uniformSpinPrior N : Measure (Spin N)) eig c I degree amp b r h =
      tensorNamespacedMeanPressure μ eig c I degree amp n b r h := by
  unfold spinPriorMeanPressure tensorNamespacedMeanPressure tensorNamespacedPressure
  simp_rw [spinPriorNamespacedLog_uniform,integral_const_mul]

end InvariantIsing

end

end OAI
