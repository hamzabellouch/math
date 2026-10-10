import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafRegularSet
import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafLusinGoodSet

namespace OAI

/-!
# Regular Lusin sets and regular maximal-inequality base points

Removing the single regularity null set from the base-point good set
does not change its measure bound. The compact Lusin set can avoid that
null set and any additional prescribed null set at the same time.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def RootLeafRegular {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0)
    (x : X n) : Prop :=
  intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x ∧
    IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
    (∀ r : ℝ, 0 < r → 0 < intrinsicRootLeaf hij μ x (Metric.ball 0 r)) ∧
    ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
      intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        basedRealMeasure (intrinsicRootLeaf hij μ x) t

theorem exists_regular_lusin_rootLeaf_good_set
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ K G : Set (X (d + 1)), IsCompact K ∧ K ⊆ Nᶜ ∧
      μ Kᶜ < ENNReal.ofReal η ∧ ContinuousOn (intrinsicLeafData hij μ hfree) K ∧
      (∀ x ∈ K, RootLeafRegular hij μ hfree x) ∧
      MeasurableSet G ∧ μ Gᶜ < ENNReal.ofReal η ∧
      (∀ x ∈ G, RootLeafRegular hij μ hfree x) ∧
      ∀ x ∈ G, ∀ r : ℝ, 0 < r →
        intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
          ENNReal.ofReal c * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r) := by
  obtain ⟨M, hM, hMzero, hregular⟩ := exists_rootLeaf_regular_nullset hij μ hfree
  obtain ⟨K, G, hK, hKN, hKsmall, hcont, _, hG, hGsmall, hreturn⟩ :=
    exists_compact_lusin_and_rootLeaf_good_set d hij μ hA hfree
      (N ∪ M) (hN.union hM) (measure_union_null hNzero hMzero) c η hc hη
  have hKreg (x : X (d + 1)) (hx : x ∈ K) : RootLeafRegular hij μ hfree x :=
    hregular x (fun hm => hKN hx (Or.inr hm))
  have hGsmall' : μ (G \ M)ᶜ < ENNReal.ofReal η := by
    rw [compl_sdiff]
    have hle : μ (Gᶜ ∪ M) ≤ μ Gᶜ := by
      simpa only [hMzero, add_zero] using measure_union_le (μ := μ) Gᶜ M
    simpa only [union_comm] using hle.trans_lt hGsmall
  exact ⟨K, G \ M, hK, fun _ hx hn => hKN hx (Or.inl hn), hKsmall, hcont,
    hKreg, hG.diff hM, hGsmall', fun x hx => hregular x hx.2,
    fun x hx => hreturn x hx.1⟩

end DukePrimeDegree

end

end OAI
