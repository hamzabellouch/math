import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalLogCoefficients
import OAI.Probability.InvariantIsing.Cavity.CavityConstantHaarLog

namespace OAI

/-! Random coefficient replacement on the canonical physical cavity
space, with the independent compression coordinate integrated out. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_canonical_log_coefficients {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ r, 0<N r) (k : ℕ → Fin m → ℕ)
    (e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r))
    (a₀ : Fin d → Fin m) (hk : ∀ r a, d ≤ k r a)
    (hgroups : ∀ r a, 0<cavityBaseGroupDimension (k r) a₀ a)
    (μ : (r : ℕ) → Measure (Orthogonal (N r))) [∀ r, IsProbabilityMeasure (μ r)]
    (θ : (r : ℕ) → Measure (LabeledTree (depth r))) [∀ r, IsProbabilityMeasure (θ r)]
    (μG : (r : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k r) a₀ a)))
    [∀ r a, IsProbabilityMeasure (μG r a)] [∀ r a, (μG r a).IsMulRightInvariant]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ) (u : ℕ → ℕ → ℝ)
    {c : ℝ} (hc : 0<c)
    (hfrac : ∀ r a, c ≤ (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r)
    (Z : ℕ → Type*) [∀ r, MeasurableSpace (Z r)]
    (P : (r : ℕ) → Measure (Z r)) [∀ r, IsProbabilityMeasure (P r)]
    (A : (r : ℕ) → Z r → CavityFactorBlocks d n) (hA : ∀ r, Measurable (A r))
    (A₁ : CavityFactorBlocks d n) {D : ℝ} (hD : 0≤D)
    (hAb : ∀ r z, cavityFactorSize (A r z).1 (A r z).2.1 (A r z).2.2 ≤ D)
    (hA₁ : cavityFactorSize A₁.1 A₁.2.1 A₁.2.2 ≤ D)
    (hprob : ∀ ε>0, Tendsto (fun r => (P r).real
      {z | ε<cavityFactorDeviation (A r z) A₁}) atTop (𝓝 0))
    (cap : ℝ) (hcap : 0≤cap) (δ : ℕ → ℝ) (hδ : ∀ r, 0≤δ r)
    (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun r =>
      (∫ p, cavityRandomHaarLog (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap (δ r) (A r) p
        ∂((P r).prod (((μ r).prod (θ r)).prod gaussianCoordinates)).prod (Measure.pi (μG r))) -
      ∫ p, cavityCanonicalHaarLog (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap 0 A₁ p
        ∂(((μ r).prod (θ r)).prod gaussianCoordinates).prod (Measure.pi (μG r))) atTop (𝓝 0) := by
  let dims := fun r => cavityBaseGroupDimension (k r) a₀
  let E := fun r => cavityBaseGroupEquiv (k r) (e r) a₀
  let frames := fun r => cavityCanonicalGroupFrame (k r) (e r) a₀ (hk r)
  let eig := fun r => diagonalPerturbedEigenvalues (fun i => lam ((E r).symm i).1)
    (cavitySpectralGroup (fun i => ((E r).symm i).1)) (v r) 1
  have h := cavity_physical_penalized_log_coefficients N depth hN dims hgroups E μ θ μG
    frames (fun r a => cavityCanonicalGroupFrame_gram (k r) (e r) a₀ (hk r) a)
    eig u hc hfrac Z P A hA A₁ hD hAb hA₁ hprob (fun j => (a₀ j,j)) cap hcap δ hδ hδlim
  change Tendsto (fun r =>
    (∫ p, cavityRandomHaarLog (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap (δ r) (A r) p
      ∂((P r).prod (((μ r).prod (θ r)).prod gaussianCoordinates)).prod (Measure.pi (μG r))) -
    ∫ p, cavityRandomHaarLog (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap 0 (fun _ => A₁) p
      ∂((P r).prod (((μ r).prod (θ r)).prod gaussianCoordinates)).prod (Measure.pi (μG r)))
      atTop (𝓝 0) at h
  have he r := cavity_constant_haar_log_average (P r) (k r) (e r) a₀ (hk r)
    (μ r) (θ r) (Measure.pi (μG r)) lam (v r) (u r) 1 cap 0 hcap A₁
  exact h.congr (fun r => by rw [he r])

end InvariantIsing

end

end OAI
