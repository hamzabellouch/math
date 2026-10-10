import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafPairSelection

namespace OAI

/-!
# Lusin sets with uniform leafwise return control

The compact Lusin set and the maximal-inequality good set can be chosen
together. This supplies the two large sets used to select shearing
returns in EKL (2006), Section 4.3.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_compact_lusin_and_rootLeaf_good_set
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ K G : Set (X (d + 1)), IsCompact K ∧ K ⊆ Nᶜ ∧
      μ Kᶜ < ENNReal.ofReal η ∧ ContinuousOn (intrinsicLeafData hij μ hfree) K ∧
      (∀ x ∈ K, intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x) ∧
      MeasurableSet G ∧ μ Gᶜ < ENNReal.ofReal η ∧
      ∀ x ∈ G, ∀ r : ℝ, 0 < r →
        intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ closedBall 0 r) ≤
          ENNReal.ofReal c * intrinsicRootLeaf hij μ x (closedBall 0 r) := by
  obtain ⟨δ, hδ, hgood⟩ := exists_large_rootLeaf_good_set d hij μ hA c η hc hη
  let ε : ℝ≥0∞ := min (ENNReal.ofReal δ) (ENNReal.ofReal η)
  have hε : ε ≠ 0 := by
    apply ne_of_gt
    exact lt_min (ENNReal.ofReal_pos.mpr hδ) (ENNReal.ofReal_pos.mpr hη)
  obtain ⟨K, hK, hKN, hKsmall, hcont, hkernel⟩ :=
    exists_compact_continuous_rootLeafData hij μ hfree N hN hNzero ε hε
  have hKδ : μ Kᶜ < ENNReal.ofReal δ := hKsmall.trans_le (min_le_left _ _)
  obtain ⟨G, hG, hGsmall, hreturn⟩ := hgood Kᶜ hK.measurableSet.compl hKδ
  exact ⟨K, G, hK, hKN, hKsmall.trans_le (min_le_right _ _), hcont, hkernel,
    hG, hGsmall, hreturn⟩

end DukePrimeDegree

end

end OAI
