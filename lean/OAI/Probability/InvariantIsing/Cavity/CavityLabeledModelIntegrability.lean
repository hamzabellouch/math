import OAI.Probability.InvariantIsing.Cavity.CavityLabeledPriorTransport
import OAI.Probability.InvariantIsing.Cavity.CavityRootedReplicaTransport

namespace OAI

/-! Exponential integrability of the literal finite labeled cavity model,
derived from the Gaussian quadratic calculation on the original model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

theorem cavity_labeled_model_integrability {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    ∀ᵐ ω ∂cavityLabeledDisorderLaw n b S₀ S,
      Integrable (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
        (cavityLabeledPriorKernel n (H n) π ω) ∧
      ((cavityLabeledPriorKernel n (H n) π ω).tilted
        (fun x => cavityLabeledPotential n K L C (ω,x))).map (cavityLabeledRootMap n ω) =
        cavityRootedFullGibbs n K (H n) L C π (cavityLabeledNoiseDisorderMap n ω) := by
  have hI := cavity_rooted_full_integrability n K H S b S₀ hS₀ L C
    hbCascade hK hH hS hb hdet hΔ hQ hR hQR π
  have hi := (cavity_labeled_noise_disorder_law n b S₀ S).quasiMeasurePreserving.ae hI
  filter_upwards [hi, cavity_labeled_disorder_good n b S₀ S hbCascade] with ω hω hg
  exact ⟨cavity_labeled_model_exp_integrable n K (H n) L C π ω hg.1 hg.2 hω.2,
    cavity_labeled_model_tilted_law n K (H n) L C π ω hg.1 hg.2 hω.2⟩

end InvariantIsing

end

end OAI
