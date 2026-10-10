import OAI.Probability.InvariantIsing.Cavity.CavityProjectorGibbsHaar

namespace OAI

/-! The coupled physical base Gibbs law has the original Haar spectral
law, jointly with the compression data and selected special axes. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_physical_gibbs_original_haar {N n m d depth r : ℕ}
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (l w : Fin m → ℕ)
    (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val < w a)
    (hln : ∀ a, l a+n ≤ w a) (hw : ∀ a, w a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ)
    (F : ((Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d) →
      (Fin r → Spin N × LabeledLeaf depth) → ℝ)
    (hF : Measurable (Function.uncurry F)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ p σ, |F p σ| ≤ C) :
    (∫ U, cavityProjectorReplicaMean T (fun a => t*lam a+2*perturbationScale N*v a) u
      (fun p => F (cavityCompressionGrams g U,p))
      (cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U) ∂μ) =
    ∫ U, ∫ V, ∫ z, referenceReplicaMean
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (cavityRotationHamiltonian (matrixRotation V⁻¹)
        (diagonalPerturbedEigenvalues
          (fun j => lam (Sum.elim (fun w => w.1) a₀ (e.symm j)))
          (cavityBaseGroup k e a₀) v t) (cavityBaseGroup k e a₀) u z)
      (F (cavityCompressionGrams g U,
        cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)))
      ∂gaussianCoordinates ∂ν ∂μ := by
  rw [cavity_physical_gibbs_projector_haar g k ek e es B₀ a₀ l w hg hln hw μ ν T
    (fun a => t*lam a+2*perturbationScale N*v a) u F hF hC hb]
  apply integral_congr_ae
  apply ae_of_all
  intro U
  apply integral_congr_ae
  apply ae_of_all
  intro V
  exact cavity_canonical_projector_replica k e a₀ V T lam v u t
    (fun p => F (cavityCompressionGrams g U,p))

end InvariantIsing

end

end OAI
