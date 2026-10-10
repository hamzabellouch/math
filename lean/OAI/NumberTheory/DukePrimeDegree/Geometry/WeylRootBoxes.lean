import OAI.NumberTheory.DukePrimeDegree.Dynamics.WeylAtomicRoots
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootTranslateBox

namespace OAI

/-! # Reindexing actual root boxes without changing the root parameter

A coordinate permutation carries the pivot, transverse slice, and quotient
root box to their permuted versions.  The real root coordinate is unchanged,
so disintegration transports the conditional measure without a rescaling.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rootSliceReindexHomeomorph {n : ℕ} (e : Equiv.Perm (Fin n))
    (i j k : Fin n) : RootSlice i j k ≃ₜ RootSlice (e i) (e j) (e k) where
  toFun s := ⟨reindexSpecialLinear ℝ e s.val, by
    change s.val.val (e.symm (e k)) (e.symm (e i)) ≠ 0 ∧
      s.val.val (e.symm (e k)) (e.symm (e j)) = 0
    simpa only [e.symm_apply_apply] using s.prop⟩
  invFun s := ⟨reindexSpecialLinear ℝ e.symm s.val, by
    change s.val.val (e k) (e i) ≠ 0 ∧ s.val.val (e k) (e j) = 0
    exact s.prop⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    ext a b
    change s.val.val (e.symm (e a)) (e.symm (e b)) = s.val.val a b
    rw [e.symm_apply_apply, e.symm_apply_apply]
  right_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    ext a b
    change s.val.val (e (e.symm a)) (e (e.symm b)) = s.val.val a b
    rw [e.apply_symm_apply, e.apply_symm_apply]
  continuous_toFun := ((continuous_reindexSpecialLinear e).comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_reindexSpecialLinear e.symm).comp
    continuous_subtype_val).subtype_mk _

def rootReindexCoordinates {n : ℕ} (e : Equiv.Perm (Fin n)) (i j k : Fin n) :
    (RootSlice i j k × ℝ) ≃ₜ (RootSlice (e i) (e j) (e k) × ℝ) :=
  (rootSliceReindexHomeomorph e i j k).prodCongr (Homeomorph.refl ℝ)

lemma rootReindexCoordinates_param {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j k : Fin n} (hij : i ≠ j) (z : RootSlice i j k × ℝ) :
    rootQuotientParametrization (e.injective.ne hij) (rootReindexCoordinates e i j k z) =
      quotientReindex e (rootQuotientParametrization hij z) := by
  change Quotient.mk _ ((reindexSpecialLinear ℝ e z.1.val) *
    Matrix.SpecialLinearGroup.transvection (e.injective.ne hij) z.2) =
      Quotient.mk _ (reindexSpecialLinear ℝ e
        (z.1.val * Matrix.SpecialLinearGroup.transvection hij z.2))
  rw [map_mul, reindex_transvection]

namespace RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

def reindex (B : PrimeDegreePackets.RootBox hij k) (e : Equiv.Perm (Fin n)) :
    PrimeDegreePackets.RootBox (e.injective.ne hij) (e k) := by
  let S := rootSliceReindexHomeomorph e i j k
  let E := rootReindexCoordinates e i j k
  have hiff (z : RootSlice i j k × ℝ) :
      z ∈ B.domain ↔ E z ∈ (S '' B.transverse) ×ˢ B.time := by
    change (z.1 ∈ B.transverse ∧ z.2 ∈ B.time) ↔
      (S z.1 ∈ S '' B.transverse ∧ z.2 ∈ B.time)
    rw [S.injective.mem_set_image]
  let eb := E.subtype hiff
  refine ⟨S '' B.transverse, B.time, S.isOpenMap _ B.transverse_open,
    B.time_open, ?_⟩
  have H := (quotientReindexHomeomorph e).isOpenEmbedding.comp
    (B.embedding.comp eb.symm.isOpenEmbedding)
  convert H using 1
  funext z
  have he : E (eb.symm z).val = z.val := congrArg Subtype.val (eb.apply_symm_apply z)
  change rootQuotientParametrization (e.injective.ne hij) z.val =
    quotientReindex e (rootQuotientParametrization hij (eb.symm z).val)
  rw [← he]
  exact rootReindexCoordinates_param e hij _

lemma reindex_domain (B : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) :
    (reindex B e).domain = rootReindexCoordinates e i j k '' B.domain := by
  ext z
  constructor
  · rintro ⟨⟨s, hs, hse⟩, ht⟩
    exact ⟨(s, z.2), ⟨hs, ht⟩, Prod.ext hse rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z.1, hz.1, rfl⟩, hz.2⟩

theorem reindex_coordinateMeasure (B : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) (μ : Measure (X n)) :
    (reindex B e).coordinateMeasure (μ.map (quotientReindex e)) =
      (B.coordinateMeasure μ).map (rootReindexCoordinates e i j k) := by
  let E := rootReindexCoordinates e i j k
  let Q := quotientReindexHomeomorph e
  ext S hS
  rw [PrimeDegreePackets.RootBox.coordinateMeasure_apply _ _ hS,
    Measure.map_apply E.measurable hS,
    PrimeDegreePackets.RootBox.coordinateMeasure_apply _ _ (E.measurable hS)]
  have he : rootQuotientParametrization (e.injective.ne hij) ''
        (S ∩ (reindex B e).domain) =
      Q '' (rootQuotientParametrization hij '' (E ⁻¹' S ∩ B.domain)) := by
    rw [reindex_domain]
    ext x
    constructor
    · rintro ⟨z, ⟨hzS, w, hw, rfl⟩, rfl⟩
      exact ⟨rootQuotientParametrization hij w, ⟨w, ⟨hzS, hw⟩, rfl⟩,
        (rootReindexCoordinates_param e hij w).symm⟩
    · rintro ⟨_, ⟨w, ⟨hwS, hw⟩, rfl⟩, rfl⟩
      exact ⟨E w, ⟨hwS, ⟨w, hw, rfl⟩⟩, rootReindexCoordinates_param e hij w⟩
  change (μ.map Q) (rootQuotientParametrization (e.injective.ne hij) ''
    (S ∩ (reindex B e).domain)) = _
  rw [he, Q.isOpenEmbedding.measurableEmbedding.map_apply, Q.injective.preimage_image]

theorem reindex_marginal (B : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) (μ : Measure (X n)) :
    ((reindex B e).coordinateMeasure (μ.map (quotientReindex e))).fst =
      ((B.coordinateMeasure μ).fst).map (rootSliceReindexHomeomorph e i j k) := by
  rw [reindex_coordinateMeasure]
  exact fst_map_measurableEquiv (B.coordinateMeasure μ)
    (rootSliceReindexHomeomorph e i j k).toMeasurableEquiv
    (MeasurableEquiv.refl ℝ)

theorem reindex_conditionalKernel (B : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      (reindex B e).conditionalKernel (μ.map (quotientReindex e))
        (rootSliceReindexHomeomorph e i j k s) = B.conditionalKernel μ s := by
  simp only [PrimeDegreePackets.RootBox.conditionalKernel, reindex_coordinateMeasure]
  have H := condKernel_map_measurableEquiv (B.coordinateMeasure μ)
    (rootSliceReindexHomeomorph e i j k).toMeasurableEquiv
    (MeasurableEquiv.refl ℝ)
  change ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
    ((B.coordinateMeasure μ).map (rootReindexCoordinates e i j k)).condKernel
      (rootSliceReindexHomeomorph e i j k s) =
        ((B.coordinateMeasure μ).condKernel s).map id at H
  simpa only [Measure.map_id] using H

end RootBox
end DukePrimeDegree

end

end OAI
