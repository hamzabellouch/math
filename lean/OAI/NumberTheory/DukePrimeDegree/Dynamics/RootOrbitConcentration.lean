import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitConcentration
import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientNeighborhoods
import OAI.NumberTheory.DukePrimeDegree.Dynamics.StrongReturns

namespace OAI

/-!
# Root-pair orbit concentration from strong returns

This is the arithmetic-quotient specialization of the compact-return
argument in EKL (2006), Proposition 4.3. The countable ergodic action may
be a dense subgroup of the neutral diagonal group. A positive-measure
set with strong returns forces the component onto one root-pair orbit.
-/

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootPair_orbit_of_strong_returns
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (H : Type*) [Group H] [Countable H]
    (φ : H →* MulOpposite (rootPairCentralizer hij))
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hE : let := rightSubgroupAction (rootPairCentralizer hij)
      let := MulAction.compHom (X (d + 1)) φ
      ErgodicSMul H (X (d + 1)) μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K) (hpos : μ K ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (hstrong : ∀ x ∈ K, ∀ h : H, rightAction x ((φ h).unop : G (d + 1)) ∈ K →
      ∀ g ∈ matrixBall (d + 1) r,
        rightAction x g = rightAction x ((φ h).unop : G (d + 1)) →
          g ∈ rootPairCentralizer hij) :
    ∃ z : X (d + 1), ∀ᵐ y ∂μ,
      ∃ c : rootPairCentralizer hij, rightAction z (c : G (d + 1)) = y := by
  let := rightSubgroupAction (rootPairCentralizer hij)
  let := rightSubgroupAction_continuous (rootPairCentralizer hij)
  let := MulAction.compHom (X (d + 1)) φ
  let : MeasurableConstSMul H (X (d + 1)) :=
    ⟨fun h => (continuous_rightAction ((φ h).unop : G (d + 1))).measurable⟩
  let : ErgodicSMul H (X (d + 1)) μ := hE
  have hμK : μ.restrict K ≠ 0 := by
    intro hz
    have he := congrArg (fun ν : Measure (X (d + 1)) => ν univ) hz
    exact hpos (by simpa using he)
  obtain ⟨z, hz⟩ := Measure.nonempty_support hμK
  obtain ⟨V, hV, hzV, hrel⟩ := exists_open_matrix_relative_lifts z hr
  let L : Set (MulOpposite (rootPairCentralizer hij)) :=
    {c | (c.unop : G (d + 1)) ∈ matrixClosedBall (d + 1) r}
  have hL : IsCompact L := by
    have he : Topology.IsClosedEmbedding
        (fun c : MulOpposite (rootPairCentralizer hij) => (c.unop : G (d + 1))) :=
      (rootPairCentralizer_isClosed hij).isClosedEmbedding_subtypeVal.comp
        MulOpposite.opHomeomorph.symm.isClosedEmbedding
    exact he.isCompact_preimage (isCompact_matrixClosedBall (d + 1) r)
  have hret : ∀ u ∈ K ∩ V, ∀ h : H, h • u ∈ K ∩ V →
      ∃ c ∈ L, c • u = h • u := by
    intro u hu h hh
    obtain ⟨g, hg, hgu⟩ := hrel u hu.2 (h • u) hh.2
    have hgC : g ∈ rootPairCentralizer hij := hstrong u hu.1 h hh.1 g hg hgu
    refine ⟨MulOpposite.op ⟨g, hgC⟩, ?_, ?_⟩
    · exact matrixBall_subset_matrixClosedBall hr.le hg
    · exact hgu
  have hconc := ae_on_single_orbit_of_compact_returns μ φ (fun _ _ => rfl)
    K hK z hz V hV hzV L hL hret
  refine ⟨z, ?_⟩
  filter_upwards [hconc] with y hy
  obtain ⟨c, hc⟩ := hy
  exact ⟨c.unop, hc⟩

end DukePrimeDegree

end

end OAI
