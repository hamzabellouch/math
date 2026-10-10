import OAI.Probability.InvariantIsing.Cavity.CavityResidual
import OAI.Probability.InvariantIsing.Cavity.CavityInnovationLeaves

namespace OAI

/-! The residual determinant contribution to the full quadratic normalizer. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma cavity_noiseLeafTerminal_sum {d : ℕ} (n : ℕ)
    (X : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (s : EuclideanSpace ℝ (Fin d))
    (v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) :
    noiseLeafTerminal n X (fun _ p => p.1 + p.2) s v = X n (cavityLeafSum n s v) := by
  induction n generalizing X s with
  | zero => rfl
  | succ n ih => exact ih (fun i => X (i + 1)) (s + v.2.1) v.2.2

lemma cavity_residual_terminal_value {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hK : K.IsHermitian) (hH : (H n).PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) :
    Real.exp (cavityQuadraticValue n K H b n s - Real.log (1 - H n * K).det / 2) =
      ∫ z : EuclideanSpace ℝ (Fin d),
        Real.exp (⟪s + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (s + z)⟫ / 2)
          ∂multivariateGaussian 0 (H n) := by
  rw [cavity_residual_integral K (H n) hK hH hQ s,
    cavityQuadraticValue_terminal]
  congr 1
  ring

theorem cavity_quadratic_root_log_integral_add_const {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef) (a : ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef) :
    let μ := cavityGaussianMarks S
    let X := fun i z => cavityQuadraticValue n K H b i z + a
    let u := fun (_ : ℕ) (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => p.1 + p.2
    let P := (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _)
    let F := fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      Real.log ((noiseTreeFactor n b μ X u p.1 p.2).toReal /
        (noiseTreeTotal _ n p.2).toReal)
    Integrable F ((multivariateGaussian 0 S₀).prod P) ∧
      (∫ p, F p ∂(multivariateGaussian 0 S₀).prod P) =
        Matrix.trace (S₀ * cavityBackwardQuadratic K (H 0)) / 2 -
          (∑ j ∈ Finset.range n, cavityDeterminantStep K H b j) + a := by
  dsimp only
  let μ := cavityGaussianMarks S
  let X := fun i z => cavityQuadraticValue n K H b i z + a
  let u := fun (_ : ℕ) (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => p.1 + p.2
  let P : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n) := noiseCascadeLaw _ n b μ
  have : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let F := fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
    Real.log ((noiseTreeFactor n b μ X u p.1 p.2).toReal /
      (noiseTreeTotal _ n p.2).toReal)
  let c := fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
  have hc : ∀ i, Measurable (c i) := fun i => measurable_cavityQuadraticStepWeight _ _ _ _
  have hXm : ∀ i, Measurable (X i) := fun i =>
    (measurable_cavityQuadraticValue n K H b i).add_const a
  have hu : ∀ i, Measurable (u i) := fun _ => measurable_fst.add measurable_snd
  have htel (i : ℕ) (s z : EuclideanSpace ℝ (Fin d)) :
      c i (s, z) = Real.exp (X (i + 1) (u i (s, z)) - X i s) := by
    dsimp only [c]
    rw [cavityQuadraticStepWeight_telescoping n K H b i s z]
    congr 1
    dsimp [X, u]
    ring
  have hm (i : ℕ) (s : EuclideanSpace ℝ (Fin d)) :
      (∫⁻ z, ENNReal.ofReal (c i (s, z) ^ b i) ∂(μ i : Measure _)) = 1 :=
    cavity_quadratic_step_fractional_moment K (H i) (H (i + 1)) (S i) hK (hH (i + 1))
      (hS i) (b i) (hb i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i) s
  have hcore (s : EuclideanSpace ℝ (Fin d)) :=
    noiseCascade_log_integral n b hbCascade μ hc hu htel hm s
  have hF : Measurable F :=
    (((measurable_noiseTreeFactor n b μ hXm hu).ennreal_toReal).div
      (((measurable_noiseTreeTotal _ n).comp measurable_snd).ennreal_toReal)).log
  have hiX : Integrable (X 0) (multivariateGaussian 0 S₀) :=
    (cavityQuadraticValue_root_integrable n K H b S₀).add (integrable_const a)
  have h := cavity_joint_integral_of_centered_square (multivariateGaussian 0 S₀) P F (X 0)
    hF (hXm 0) hiX (fun s => (hcore s).2.2.2.1)
    ⟨_, fun s => (hcore s).2.2.2.2⟩ (fun s => (hcore s).2.2.1)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  change (∫ s, cavityQuadraticValue n K H b 0 s + a ∂multivariateGaussian 0 S₀) = _
  rw [integral_add (cavityQuadraticValue_root_integrable n K H b S₀) (integrable_const _),
    cavityQuadraticValue_root_integral n K H b S₀ hS₀, integral_const, probReal_univ, one_smul]

end InvariantIsing

end

end OAI
