import OAI.NumberTheory.DukePrimeDegree.Geometry.NextGroupCoordinates

namespace OAI

/-! # Conjugation preserves the intrinsic product on the actual next subgroup -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

lemma next_conjugation_mem (d : ℕ) (q : InitialRootStep (d+1))
    (g : positiveRootGeneratedGroup (q.remaining.erase q.root)) (r : ℝ) :
    Matrix.SpecialLinearGroup.transvection q.distinct (-r) * g.val *
      Matrix.SpecialLinearGroup.transvection q.distinct r ∈
        positiveRootGeneratedGroup (q.remaining.erase q.root) := by
  let w : positiveRootGeneratedGroup q.remaining :=
    ⟨g.val,positiveRootGeneratedGroup_mono (Finset.erase_subset _ _) g.prop⟩
  let u : positiveRootGeneratedGroup q.remaining :=
    ⟨Matrix.SpecialLinearGroup.transvection q.distinct (-r),
      transvection_mem_positiveRootGeneratedGroup _ q.distinct q.mem_remaining (-r)⟩
  have hg : w ∈ (positiveRootGeneratedGroup (q.remaining.erase q.root)).comap
      (positiveRootGeneratedGroup q.remaining).subtype := g.prop
  have hn := (q.next_normal d).conj_mem w hg u
  change u.val * w.val * u.val⁻¹ ∈ positiveRootGeneratedGroup (q.remaining.erase q.root) at hn
  simpa only [u,w,Matrix.SpecialLinearGroup.transvection_inv,neg_neg] using hn

def nextConjugation (d : ℕ) (q : InitialRootStep (d+1)) (r : ℝ)
    (g : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    positiveRootGeneratedGroup (q.remaining.erase q.root) :=
  ⟨Matrix.SpecialLinearGroup.transvection q.distinct (-r) * g.val *
    Matrix.SpecialLinearGroup.transvection q.distinct r,q.next_conjugation_mem d g r⟩

lemma continuous_nextConjugation (d : ℕ) (q : InitialRootStep (d+1)) (r : ℝ) :
    Continuous (q.nextConjugation d r) :=
  ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

lemma nextConjugation_coordinates (d : ℕ) (q : InitialRootStep (d+1)) (r : ℝ)
    (g : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    q.nextGroupCoordinates (q.nextConjugation d r g) =
      q.rowShear (-r) (q.nextGroupCoordinates g) := by
  funext p
  rw [q.nextGroupCoordinates_apply]
  have he : q.nextGroupCoordinates g = fun z => g.val.val z.val.1 z.val.2 := by
    funext z
    exact q.nextGroupCoordinates_apply g z
  rw [he,q.rowShear_eq_conjugation_entries]
  rfl

def nextIntrinsicProduct (d : ℕ) (q : InitialRootStep (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ] (x : X (d+1)) :
    Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)) :=
  (Measure.pi fun p : q.NextRoot =>
    intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ x).map
      q.nextGroupCoordinates.symm

end InitialRootStep

theorem ae_nextIntrinsicProduct_conjugation (d : ℕ) (q : InitialRootStep (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hna : ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf q.distinct μ x)) :
    ∀ᵐ x ∂μ, ∀ r : ℝ,
      (q.nextIntrinsicProduct d μ x).map (q.nextConjugation d r) = q.nextIntrinsicProduct d μ x := by
  filter_upwards [ae_intrinsic_rowShear_preserves d q μ hna] with x hx
  intro r
  let ν := Measure.pi fun p : q.NextRoot =>
    intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ x
  have he : q.nextConjugation d r ∘ q.nextGroupCoordinates.symm =
      q.nextGroupCoordinates.symm ∘ q.rowShear (-r) := by
    funext z
    apply q.nextGroupCoordinates.injective
    simp only [Function.comp_apply,q.nextConjugation_coordinates,
      q.nextGroupCoordinates.apply_symm_apply]
  change (ν.map q.nextGroupCoordinates.symm).map (q.nextConjugation d r) =
    ν.map q.nextGroupCoordinates.symm
  rw [Measure.map_map (q.continuous_nextConjugation d r).measurable
    q.nextGroupCoordinates.symm.measurable]
  change ν.map (q.nextConjugation d r ∘ q.nextGroupCoordinates.symm) = _
  rw [he,←Measure.map_map q.nextGroupCoordinates.symm.measurable
    (hx (-r)).measurable,(hx (-r)).map_eq]

end DukePrimeDegree

end

end OAI
