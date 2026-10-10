import OAI.Combinatorics.Progressions.Estimates.NormalizedSmallLiftHaar
import OAI.Combinatorics.Progressions.Geometry.QuantitativeProjectedChart

namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped BigOperators

theorem exists_local_lattice_chart {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    let n := finrank ℝ Wᗮ
    let C : ℝ := 20 * ((n : ℝ) + 1) ^ 3
    ∃ b : Basis (Fin n) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∀ i, 0 < basisAxisScale b i) ∧
      (∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ Real.exp C * ‖x‖) ∧
      (∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ Real.exp C * ‖p‖) ∧
      Real.exp (-C) ≤
        ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ∧
      ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ≤ Real.exp C ∧
      ∀ (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice J) W).toAddSubgroup))
        [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
        (Ω : Set (EuclideanSpace ℝ J)), MeasurableSet Ω → Ω ⊆ standardLatticeSmallBox J →
        μ (latticeSmallLiftRegion (standardEuclideanLattice J) W Ω) =
          (∑' z : Fin n → ℤ, volume {u : W |
            (normalizedOrthogonalChart W b).symm
              (u, fun i => (z i : ℝ) / (basisAxisScale b i : ℝ)) ∈ Ω}) /
            ENNReal.ofReal (ZLattice.covolume (latticeSection (standardEuclideanLattice J) W)) := by
  obtain ⟨b, hb, hK, hf, hi, hlo, hhi⟩ := exists_quantitative_projected_chart W
  refine ⟨b, hb, hK, hf, hi, hlo, hhi, ?_⟩
  intro μ _ _ Ω hΩm hΩ
  exact normalized_smallLift_haar_formula W b hb μ hΩm hΩ

end Erdos3

end

end OAI
