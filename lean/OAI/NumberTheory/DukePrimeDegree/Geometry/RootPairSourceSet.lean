import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPairTimeSelection

namespace OAI

/-!
# A positive-measure source for synchronized recurrence

The maximal estimates leave positive measure whenever their explicit
error budget is below one. Any prescribed null set can be removed
without losing positivity or the simultaneous recurrence and covariance
properties.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_positive_rootPair_source_set
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (G H N : Set (X (d + 1))) (hG : MeasurableSet G) (hH : MeasurableSet H)
    (hN : MeasurableSet N) (hNzero : μ N = 0)
    (ε : ℝ) (hε : 0 < ε)
    (hbudget : ENNReal.ofReal (2 * μ.real Gᶜ / ε) +
      ENNReal.ofReal (2 * μ.real Hᶜ / ε) < 1) :
    ∃ Z : Set (X (d + 1)), MeasurableSet Z ∧ μ Z ≠ 0 ∧ Z ⊆ Nᶜ ∧
      ∀ z ∈ Z,
        (∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree z t) ∧
        ∀ T : ℝ, 1 ≤ T →
          volume.real (Ioc 0 T ∩ {t | rightAction z (rootPairFlow i j (-t)) ∉ G}) ≤ ε * T ∧
          volume.real (Ioc 0 T ∩ {t | rightAction z (rootPairFlow i j (-t)) ∉ H}) ≤ ε * T := by
  obtain ⟨Z, hZ, hZsmall, hgood⟩ := exists_rootPair_two_target_covariance_set
    d hij μ hA hfree G H hG hH ε hε
  have hZpos : μ Z ≠ 0 := by
    intro hzero
    have htotal := prob_add_prob_compl (μ := μ) hZ
    rw [hzero, zero_add] at htotal
    exact (hZsmall.trans_lt hbudget).ne htotal
  refine ⟨Z \ N, hZ.diff hN, ?_, fun _ hx => hx.2, ?_⟩
  · rwa [measure_sdiff_null hNzero]
  · exact fun z hz => hgood z hz.1

end DukePrimeDegree

end

end OAI
