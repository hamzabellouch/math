import OAI.Probability.InvariantIsing.Magnetic.RestrictedPhysicalCutoff
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffTightness

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical Matrix MatrixOrder Matrix.Norms.L2Operator
namespace InvariantIsing

theorem restricted_full_special_cutoff_error {N n m d depth : ℕ}
    (S : Finset (Spin (N+n))) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal (N + n))) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin (N + n) → ℝ) (g : Fin (N + n) → Fin m)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hmB : Measurable B) (R : ℝ)
    (F : SpecialOrthogonal (N + n) → (Fin 2 → Spin (N + n) × LabeledLeaf depth) → ℝ)
    (hmF : Measurable (Function.uncurry F))
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ U σ, |F U σ| ≤ M) :
    |restrictedCavityFullCutoffDisorderTest S hS μ T eig (cavitySpectralGroup g) u
        (cavitySpecialCutoff g B R) F - restrictedCavityFullDisorderTest S hS μ T eig (cavitySpectralGroup g) u F| ≤
      4 * M * restrictedCavityFullDisorderTest S hS μ T eig (cavitySpectralGroup g) u
        (fun U σ => if R < ‖cavityFullSpecialCoordinates g (B U) U (σ 0).1‖ then 1 else 0) := by
  simpa only [cavitySpecialCutoff, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] using
    restricted_cavity_full_cutoff_error S hS μ T eig (cavitySpectralGroup g) u hu
      (cavitySpecialCutoff g B R) (measurableSet_cavitySpecialCutoff g B hmB R) F hmF hM hF

end InvariantIsing

end

end OAI
