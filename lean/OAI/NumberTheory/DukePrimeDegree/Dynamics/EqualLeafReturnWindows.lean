import OAI.NumberTheory.DukePrimeDegree.Dynamics.EqualLeafReturns

namespace OAI

/-!
# Equal-leaf return sequences with arbitrarily long shearing windows

Passing to a tail of the actual noncentral return sequence makes its
scale at most one and its logarithmic window exceed any fixed bound.
The common source set and equality of intrinsic leaves are preserved.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_equal_leaf_return_sequence_with_windows
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K) (hpos : μ K ≠ 0) (L : ℝ) :
    ∃ (x y : ℕ → X (d + 1)) (g : ℕ → G (d + 1)),
      Tendsto g atTop (𝓝 1) ∧ ∀ m,
        x m ∈ K ∧ y m ∈ K ∧ rightAction (x m) (g m) = y m ∧
        (¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
          Matrix.SpecialLinearGroup.transvection hij t * g m) ∧
        intrinsicRootLeaf hij μ (x m) = intrinsicRootLeaf hij μ (y m) ∧
        rootShearingKappa i j (g m) ≤ 1 ∧ L ≤ rootShearingLogTime i j (g m) := by
  obtain ⟨x, y, g, hg, hp⟩ := exists_equal_leaf_noncentral_return_sequence d hd hij μ hA K hK hpos
  have hnot (m : ℕ) := (hp m).2.2.2.1
  have hk : Tendsto (fun m => rootShearingKappa i j (g m)) atTop (𝓝 0) := by
    change Tendsto (rootShearingKappa i j ∘ g) atTop (𝓝 0)
    simpa only [rootShearingKappa_one hij] using
      ((continuous_rootShearingKappa i j).tendsto 1).comp hg
  have hs : ∀ᶠ m in atTop, rootShearingKappa i j (g m) < 1 :=
    (tendsto_order.1 hk).2 1 zero_lt_one
  have hw : ∀ᶠ m in atTop, L ≤ rootShearingLogTime i j (g m) :=
    (rootShearingLogTime_tendsto hij g hg hnot).eventually_ge_atTop L
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hs.and hw)
  refine ⟨fun m => x (m + M), fun m => y (m + M), fun m => g (m + M),
    hg.comp (tendsto_add_atTop_nat M), ?_⟩
  intro m
  have hm := hM (m + M) (by omega)
  exact ⟨(hp (m + M)).1, (hp (m + M)).2.1, (hp (m + M)).2.2.1,
    (hp (m + M)).2.2.2.1, (hp (m + M)).2.2.2.2, hm.1.le, hm.2⟩

end DukePrimeDegree

end

end OAI
