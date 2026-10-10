import OAI.Probability.InvariantIsing.Cavity.CavityRandomHaarLog
import OAI.Probability.InvariantIsing.Cavity.CavityExtraLogAverage

namespace OAI

/-! An independent compression coordinate disappears once its coefficient
has been replaced by the deterministic limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_constant_haar_log_average {Z : Type*} [MeasurableSpace Z]
    {N n m d depth : ℕ} (P : Measure Z) [IsProbabilityMeasure P]
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))
    [IsProbabilityMeasure η] (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (A : CavityFactorBlocks d n) :
    (∫ p, cavityRandomHaarLog k e a₀ hk lam v u t cap δ (fun _ : Z => A) p
      ∂(P.prod ((μ.prod θ).prod gaussianCoordinates)).prod η) =
    ∫ p, cavityCanonicalHaarLog k e a₀ hk lam v u t cap δ A p
      ∂((μ.prod θ).prod gaussianCoordinates).prod η := by
  let F := cavityRandomHaarLog (depth := depth) k e a₀ hk lam v u t cap δ (fun _ : Z => A)
  have hF : Measurable F :=
    measurable_cavityRandomHaarLog k e a₀ hk lam v u t cap δ _ measurable_const
  have hb p : |F p| ≤ (|t| * cavityFactorSize A.1 A.2.1 A.2.2+|δ|)*(1+N) :=
    cavityRandomHaarLog_bound k e a₀ hk lam v u t cap δ hcap _ (fun _ => le_rfl) p
  rw [cavity_bounded_extra_product_integral P ((μ.prod θ).prod gaussianCoordinates) η F hF hb]
  change (∫ _ : Z, (∫ p, cavityCanonicalHaarLog k e a₀ hk lam v u t cap δ A p
    ∂((μ.prod θ).prod gaussianCoordinates).prod η) ∂P) = _
  simp

end InvariantIsing

end

end OAI
