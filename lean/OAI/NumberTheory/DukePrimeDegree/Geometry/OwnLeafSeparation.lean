import OAI.NumberTheory.DukePrimeDegree.Dynamics.PublishedEKL

namespace OAI

/-!
# Separation along a noninvariant root leaf

This is the root-leaf separation used in EKL (2006), Lemma 4.4(2).
The projective multiplier vanishes by diagonal recurrence, and ergodicity
makes every translation period trivial unless the ambient measure is
invariant under the root group. No product-structure assertion for a larger
horospherical group is included here.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

/-- In the noninvariant ergodic case, a normalized leaf cannot equal a
nontrivial rebasing of itself. This is pointwise in the rebase parameter. -/
theorem ae_based_rootLeaf_eq_only_at_zero
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hnot : ¬ ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ x ∂μ, ∀ t : ℝ,
      basedRealMeasure (intrinsicRootLeaf hij μ x) t = intrinsicRootLeaf hij μ x → t = 0 := by
  have hA (u : LogCoordinates d) :
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have hbot : ∀ᵐ x ∂μ, realLeafPeriods (intrinsicRootLeaf hij μ x) = ⊥ :=
    (intrinsicRootLeaf_periods_ergodic_alternative d hij μ).resolve_left hnot
  filter_upwards [hbot, ae_intrinsicRootLeaf_spec hij μ hfree,
    ae_intrinsic_projective_multiplier_zero d hij μ hA] with x hb hs hm
  let ν := intrinsicRootLeaf hij μ x
  let : IsLocallyFiniteMeasure ν := hs.1
  intro t ht
  have hp := projectivePeriod_of_based_fixed ν hs.2 t ht
  have hz := hm _ hp
  have hperiod := leaf_period_of_projective_multiplier_zero ν _ hp hz
  change -t ∈ realLeafPeriods (intrinsicRootLeaf hij μ x) at hperiod
  rw [hb, AddSubgroup.mem_bot] at hperiod
  exact neg_eq_zero.mp hperiod

/-- On almost every conditional root fiber, equality of the intrinsic
leaves detects the original point in the noninvariant ergodic case. -/
theorem ae_rootLeaf_separates_own_fiber
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hnot : ¬ ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ x ∂μ, ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
      (intrinsicRootLeaf hij μ (rightAction x
        (Matrix.SpecialLinearGroup.transvection hij t)) = intrinsicRootLeaf hij μ x ↔ t = 0) := by
  have hA (u : LogCoordinates d) :
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  filter_upwards [ae_based_rootLeaf_eq_only_at_zero d hij μ hnot,
    ae_intrinsicRootLeaf_rebase hij μ hfree] with x hx hrebase
  filter_upwards [hrebase] with t ht
  constructor
  · intro heq
    exact hx t (ht.symm.trans heq)
  · rintro rfl
    simp

end DukePrimeDegree

end

end OAI
