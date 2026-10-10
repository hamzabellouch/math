import OAI.Probability.InvariantIsing.Magnetic.RestrictedProjectorHaarMean
import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientValueLimit

namespace OAI

/-! Normalized coefficient replacement for varying finite perturbation minimizers.

Normalized coefficient replacement under independent compression
and base-Haar averages. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

theorem restricted_haar_normalized_coefficient_tendsto {m d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (j : ℕ) → Finset (Spin (N j))) (hS : ∀ j, (S j).Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (k : ℕ → Fin m → ℕ)
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (a₀ : Fin d → Fin m)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n))) [∀ j, IsProbabilityMeasure (μ j)]
    (ν : (j : ℕ) → Measure (Orthogonal (N j))) [∀ j, IsProbabilityMeasure (ν j)]
    (T : (j : ℕ) → LabeledTree (depth j)) (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (A : (j : ℕ) → Orthogonal (N j+n) → CavityFactorBlocks d n)
    (hA : ∀ j, Measurable (A j)) (A₀ : CavityFactorBlocks d n)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × LabeledLeaf (depth j)) × Spin n) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ j σ, |F j σ| ≤ M)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation (A j U) A₀}) atTop (𝓝 0)) :
    Tendsto (fun j =>
      (∫ U, ∫ V, restrictedProjectorCavityMean (S j) (hS j) Cset hCset (T j)
        (fun a => t*lam a+2*perturbationScale (N j)*v j a) (u j) t D (A j U) (F j)
        (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame (k j) (e j) a₀)) ∂ν j ∂μ j) -
      ∫ _U, ∫ V, restrictedProjectorCavityMean (S j) (hS j) Cset hCset (T j)
        (fun a => t*lam a+2*perturbationScale (N j)*v j a) (u j) t D A₀ (F j)
        (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame (k j) (e j) a₀)) ∂ν j ∂μ j)
      atTop (𝓝 0) := by
  apply cavity_coefficient_values_tendsto μ A hA A₀ _ _
    (fun j => measurable_restrictedProjectorHaarMean (S j) (hS j) Cset hCset (k j) (e j) a₀ (ν j) (T j) _ (u j) t D
      (A j) (hA j) (F j))
    (fun j => measurable_restrictedProjectorHaarMean (S j) (hS j) Cset hCset (k j) (e j) a₀ (ν j) (T j) _ (u j) t D
      (fun _ => A₀) measurable_const (F j)) hM
    (show 0 ≤ 4*|t| *D by positivity)
    (fun j U => restrictedProjectorHaarMean_bound (S j) (hS j) Cset hCset (k j) (e j) a₀ (ν j) (T j) _ (u j) t D
      (A j U) (F j) hM (hF j))
    (fun j _ => restrictedProjectorHaarMean_bound (S j) (hS j) Cset hCset (k j) (e j) a₀ (ν j) (T j) _ (u j) t D
      A₀ (F j) hM (hF j))
    (fun j U s hs => restricted_projector_haar_coefficient_error (S j) (hS j) Cset hCset (k j) (e j) a₀ (ν j)
      (T j) lam (v j) (u j) (hu j) t hD (A j U) A₀ (F j) hM (hF j) hs) hprob

end InvariantIsing

end

end OAI
