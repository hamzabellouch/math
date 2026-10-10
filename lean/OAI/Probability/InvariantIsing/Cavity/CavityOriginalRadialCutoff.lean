import OAI.Probability.InvariantIsing.Cavity.CavityGeometricMean
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffTightness
import OAI.Probability.InvariantIsing.Cavity.CavityFactorScaling
import OAI.Probability.InvariantIsing.Cavity.CavityOrientation

namespace OAI

/-! The original geometric cutoff is the radial special-coordinate
cutoff under the oriented Haar law, with the exact spin split. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma cavity_original_radial_cutoff {N n m d depth : ℕ}
    (μ : Measure (Orthogonal (N+n))) (hN : 0 < N+n)
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : Measurable B) (T : LabeledTree depth) (eig : Fin (N+n) → ℝ)
    (u : ℕ → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ) :
    (∫ U, cavityOriginalGeometricMean g B T eig u (1+R^2) F
      (cavityOrientationLift hN U) ∂μ) =
    cavityFullCutoffDisorderTest (μ.map (cavityOrientationLift hN)) T eig
      (cavitySpectralGroup g) u
      (cavitySpecialCutoff g (fun U => B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) R)
      (fun _ σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) := by
  have hs (U : SpecialOrthogonal (N+n)) :
      {x : Spin (N+n) × LabeledLeaf depth | cavityGeometricWeight g
        (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
        (cavitySpinSplit N n x.1) ≤ 1+R^2} =
      cavitySpecialCutoff g
        (fun U => B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) R U := by
    have he (σ : Spin (N+n)) : cavityJoinedSpin (cavitySpinSplit N n σ) = σ := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [cavityJoinedSpin, cavitySpinSplit]
    dsimp only [cavityGeometricWeight,cavitySpecialCutoff]
    simp only [he]
    exact (cavity_radial_square_cutoff _ (fun x => norm_nonneg _) hR).symm
  have he : (fun U => cavityOriginalGeometricMean g B T eig u (1+R^2) F U) =
      fun U => ∫ z, cavityCutoffReplicaMean
        (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
        (cavityFullHamiltonian eig (cavitySpectralGroup g) u (U,z))
        (cavitySpecialCutoff g
          (fun U => B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) R U)
        (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates := by
    funext U
    simp only [cavityOriginalGeometricMean,hs]
    rfl
  rw [← integral_map_of_stronglyMeasurable (measurable_cavityOrientationLift hN)
    (measurable_cavityOriginalGeometricMean g B hB T eig u (1+R^2) F).stronglyMeasurable]
  rw [he]
  rfl

end InvariantIsing

end

end OAI
