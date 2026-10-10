import OAI.NumberTheory.DukePrimeDegree.Geometry.RootRowShear
import OAI.NumberTheory.DukePrimeDegree.Geometry.IndexedRootShear

namespace OAI

/-! # The remaining intrinsic product is invariant under extremal conjugation -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Classical
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

lemma rowShear_preserves_of_steps (q : InitialRootStep n)
    (ν : q.NextRoot → Measure ℝ)
    (hstep : ∀ p ∈ q.rowTargets, ∀ r : ℝ,
      MeasurePreserving (indexedLinearShear p (q.rowSource p) r) (Measure.pi ν) (Measure.pi ν))
    (r : ℝ) : MeasurePreserving (q.rowShear r) (Measure.pi ν) (Measure.pi ν) := by
  have aux (l : List q.NextRoot) (hl : ∀ p ∈ l, p ∈ q.rowTargets) :
      MeasurePreserving (iteratedCoordinateShear q.rowSource r l) (Measure.pi ν) (Measure.pi ν) := by
    induction l with
    | nil => exact MeasurePreserving.id _
    | cons p l ih =>
        exact (hstep p (hl p List.mem_cons_self) r).comp
          (ih (fun z hz => hl z (List.mem_cons_of_mem p hz)))
  exact aux _ (fun _ hp => Finset.mem_toList.mp hp)

end InitialRootStep

theorem ae_intrinsic_rowShear_preserves (d : ℕ) (q : InitialRootStep (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hna : ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf q.distinct μ x)) :
    ∀ᵐ x ∂μ, ∀ r : ℝ, MeasurePreserving (q.rowShear r)
      (Measure.pi fun p : q.NextRoot =>
        intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ x)
      (Measure.pi fun p : q.NextRoot =>
        intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ x) := by
  classical
  let hpos := fun p (hp : p ∈ q.remaining.erase q.root) =>
    q.remaining_positive p (Finset.mem_erase.mp hp).2
  have H (p : q.NextRoot) : ∀ᵐ x ∂μ, p ∈ q.rowTargets → ∀ r : ℝ,
      MeasurePreserving (indexedLinearShear p (q.rowSource p) r)
        (Measure.pi fun z : q.NextRoot => intrinsicRootLeaf (ne_of_lt (hpos z.val z.prop)) μ x)
        (Measure.pi fun z : q.NextRoot => intrinsicRootLeaf (ne_of_lt (hpos z.val z.prop)) μ x) := by
    by_cases hp : p ∈ q.rowTargets
    · have ha : p.val.1 = q.root.1 := (Finset.mem_filter.mp hp).2
      have hac : (q.root.1,p.val.2) ∈ q.remaining.erase q.root := by
        simpa only [←ha,Prod.mk.eta] using p.prop
      have hbc := q.row_source_mem p ha
      have he : (⟨(q.root.1,p.val.2),hac⟩ : q.NextRoot) = p :=
        Subtype.ext (Prod.ext ha.symm rfl)
      have hs : (⟨(q.root.2,p.val.2),hbc⟩ : q.NextRoot) = q.rowSource p :=
        Subtype.ext (q.rowSource_val p ha).symm
      have hh := ae_intrinsic_indexedLinearShear_preserves d (q.remaining.erase q.root)
        hpos q.distinct hbc hac μ hna
      filter_upwards [hh] with x hx
      intro _ r
      simpa only [he,hs] using hx r
    · exact Filter.Eventually.of_forall fun _ h => (hp h).elim
  filter_upwards [ae_all_iff.mpr H] with x hx
  exact q.rowShear_preserves_of_steps _ hx

end DukePrimeDegree

end

end OAI
