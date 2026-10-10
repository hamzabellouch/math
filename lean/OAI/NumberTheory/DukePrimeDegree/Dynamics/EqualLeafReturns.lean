import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralLeafVersion
import OAI.NumberTheory.DukePrimeDegree.Dynamics.NoncentralReturns

namespace OAI

/-!
# Noncentral return pairs with equal actual leaves

The strictly invariant version removes a single null set. Every neutral
pair outside it has equal intrinsic leaves, even when the neutral
parameter is chosen after the points. Applying the exceptional-set
exclusion to the remaining positive-measure set gives noncentral return
matrices tending to identity with the required equal-leaf pairs.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_neutral_leaf_equality
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ x ∉ N, ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
        rightAction x (diagonalOneParameter ell hell 1) ∉ N →
        intrinsicRootLeaf hij μ (rightAction x (diagonalOneParameter ell hell 1)) =
          intrinsicRootLeaf hij μ x := by
  obtain ⟨V, heq, _, hinv⟩ := exists_strictly_neutral_invariant_leafData d hij μ hA hfree
  have hboth := heq.and (ae_intrinsicRootKernel_eq hij μ hfree)
  obtain ⟨N, hbad, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hboth)
  have hgood (x : X (d + 1)) (hx : x ∉ N) :
      V x = intrinsicLeafData hij μ hfree x ∧
        intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x := by
    by_contra h
    exact hx (hbad h)
  refine ⟨N, hN, hzero, ?_⟩
  intro x hx ell hell hn hy
  have hxgood := hgood x hx
  have hygood := hgood _ hy
  have hdata : intrinsicLeafData hij μ hfree
      (rightAction x (diagonalOneParameter ell hell 1)) = intrinsicLeafData hij μ hfree x :=
    hygood.1.symm.trans ((hinv ell hell hn x).trans hxgood.1)
  have hk := (intrinsicLeafData_eq_iff hij μ hfree _ _).mp hdata
  exact hygood.2.symm.trans (hk.trans hxgood.2)

theorem exists_equal_leaf_noncentral_return_sequence
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K) (hpos : μ K ≠ 0) :
    ∃ (x y : ℕ → X (d + 1)) (g : ℕ → G (d + 1)),
      Tendsto g atTop (𝓝 1) ∧ ∀ m,
        x m ∈ K ∧ y m ∈ K ∧ rightAction (x m) (g m) = y m ∧
        (¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
          Matrix.SpecialLinearGroup.transvection hij t * g m) ∧
        intrinsicRootLeaf hij μ (x m) = intrinsicRootLeaf hij μ (y m) := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  obtain ⟨N, hN, hzero, hequal⟩ := exists_nullset_neutral_leaf_equality d hij μ hA hfree
  have hpos' : μ (K \ N) ≠ 0 := by rwa [measure_sdiff_null hzero]
  obtain ⟨x, y, g, hg, hp⟩ := exists_noncentral_neutral_return_sequence d hd hij μ hA
    (K \ N) (hK.diff hN) hpos'
  refine ⟨x, y, g, hg, ?_⟩
  intro m
  rcases hp m with ⟨hx, hy, hret, hnot, ell, hell, hn, hdiag⟩
  refine ⟨hx.1, hy.1, hret, hnot, ?_⟩
  have he := hequal (x m) hx.2 ell hell hn (by rw [hdiag]; exact hy.2)
  simpa only [hdiag] using he.symm

end DukePrimeDegree

end

end OAI
