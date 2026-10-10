import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafSmallRadius

namespace OAI

/-!
# Measurable small-ball good sets

Nonatomic root leaves admit a common small closed-ball radius outside a
measurable set of arbitrarily small measure. Pointwise agreement with the
intrinsic leaves is obtained by removing one measurable null set.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_rootLeaf_closedBall_good_set
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hnontrivial : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x ≠ Measure.dirac 0)
    (c ε : ℝ≥0∞) (hc : 0 < c) (hε : ε ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 2 ∧ ∃ G : Set (X (d + 1)),
      MeasurableSet G ∧ μ Gᶜ < ε ∧
      ∀ x ∈ G, intrinsicRootLeaf hij μ x (closedBall 0 ρ) < c := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  have heq : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x :=
    ae_intrinsicRootKernel_eq hij μ hfree
  obtain ⟨N, hNbad, hN, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp heq)
  obtain ⟨r, hr, hrhalf, hsmall⟩ :=
    exists_uniform_small_rootLeaf_ball d hij μ hA hnontrivial c ε hc hε
  let B := {x | c ≤ κ x (ball 0 r)}
  have hB : MeasurableSet B :=
    measurableSet_le measurable_const (κ.measurable_coe isOpen_ball.measurableSet)
  have hBmass : μ B < ε := by
    have hcongr : B =ᵐ[μ] {x | c ≤ intrinsicRootLeaf hij μ x (ball 0 r)} := by
      filter_upwards [heq] with x hx
      change (c ≤ κ x (ball 0 r)) = (c ≤ intrinsicRootLeaf hij μ x (ball 0 r))
      rw [hx]
    rwa [measure_congr hcongr]
  refine ⟨r / 2, by linarith, by linarith, (B ∪ N)ᶜ, (hB.union hN).compl, ?_, ?_⟩
  · rw [compl_compl]
    exact (measure_union_le B N).trans_lt (by simpa only [hNzero, add_zero] using hBmass)
  · intro x hx
    have hxB : x ∉ B := fun h => hx (Or.inl h)
    have hxN : x ∉ N := fun h => hx (Or.inr h)
    have hxeq : κ x = intrinsicRootLeaf hij μ x := by
      by_contra h
      exact hxN (hNbad h)
    have hmass : intrinsicRootLeaf hij μ x (ball 0 r) < c := by
      rw [← hxeq]
      exact lt_of_not_ge hxB
    exact (measure_mono (closedBall_subset_ball (by linarith : r / 2 < r))).trans_lt hmass

end DukePrimeDegree

end

end OAI
