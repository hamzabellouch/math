import OAI.NumberTheory.DukePrimeDegree.Geometry.LatticeGroupDecomposition

namespace OAI

/-!
# A normalizer acts on the actual invariant sigma algebra

The normalizer need not fix individual ergodic components. It acts
measurably on their invariant sigma algebra and preserves the trimmed
base measure. These are the base-space facts needed for covariance of
the component kernel.
-/

noncomputable section
open MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

lemma measurable_invariantSigma_of_semiconjugacy
    {H Y : Type*} [Group H] [MulAction H Y] [MeasurableSpace Y]
    (T : Y → Y) (hT : Measurable T) (α : H → H)
    (hα : ∀ h x, T (h • x) = α h • T x) :
    @Measurable Y Y (actionInvariantSigma H Y) (actionInvariantSigma H Y) T := by
  intro s hs
  have hs' (h : H) : MeasurableSet s ∧ (fun x : Y => h • x) ⁻¹' s = s :=
    (iInf_le (fun g : H => MeasurableSpace.invariants (fun x : Y => g • x)) h) s hs
  rw [actionInvariantSigma, MeasurableSpace.measurableSet_iInf]
  intro h
  refine ⟨hT (hs' 1).1, ?_⟩
  ext x
  change T (h • x) ∈ s ↔ T x ∈ s
  rw [hα]
  exact Set.ext_iff.mp (hs' (α h)).2 (T x)

lemma measurePreserving_trim_of_measurable
    {Y : Type*} [mY : MeasurableSpace Y] (m : MeasurableSpace Y)
    (hm : m ≤ mY) (μ : @Measure Y mY) (T : Y → Y)
    (hT : @MeasurePreserving Y Y mY mY T μ μ) (hmT : @Measurable Y Y m m T) :
    @MeasurePreserving Y Y m m T
      (@Measure.trim Y m mY μ hm) (@Measure.trim Y m mY μ hm) := by
  refine ⟨hmT, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hmT hs, trim_measurableSet_eq hm (hmT hs),
    trim_measurableSet_eq hm hs]
  let : MeasurableSpace Y := mY
  exact hT.measure_preimage ((hm s hs).nullMeasurableSet)

lemma lattice_normalizer_measurable_invariantSigma {n : ℕ}
    (H : Subgroup (G n)) (a : G n)
    (ha : a ∈ Subgroup.normalizer (H : Set (G n))) :
    @Measurable (X n) (X n) (actionInvariantSigma H (X n))
      (actionInvariantSigma H (X n)) (fun x => rightAction x a) := by
  let α : H → H := fun h => ⟨a⁻¹ * h.val * a,
    (Subgroup.mem_normalizer_iff''.mp ha h.val).mp h.property⟩
  apply measurable_invariantSigma_of_semiconjugacy
    (fun x => rightAction x a) (continuous_rightAction a).measurable α
  intro h x
  change rightAction (rightAction x h.val⁻¹) a =
    rightAction (rightAction x a) (a⁻¹ * h.val * a)⁻¹
  simp only [rightAction_mul]
  congr 1
  group

/-- The actual normalizer transformation preserves the component base
law whenever it preserves the ambient measure. -/
lemma lattice_normalizer_preserves_invariantSigma {n : ℕ}
    (H : Subgroup (G n)) (a : G n)
    (ha : a ∈ Subgroup.normalizer (H : Set (G n)))
    (μ : Measure (X n)) (hμ : μ.map (fun x => rightAction x a) = μ) :
    @MeasurePreserving (X n) (X n)
      (actionInvariantSigma H (X n)) (actionInvariantSigma H (X n))
      (fun x => rightAction x a)
      (μ.trim (actionInvariantSigma_le H (X n)))
      (μ.trim (actionInvariantSigma_le H (X n))) := by
  exact measurePreserving_trim_of_measurable _ _ μ _
    ⟨(continuous_rightAction a).measurable, hμ⟩
    (lattice_normalizer_measurable_invariantSigma H a ha)

end DukePrimeDegree

end

end OAI
