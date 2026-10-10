import OAI.NumberTheory.DukePrimeDegree.Geometry.WeylRootBoxes

namespace OAI

/-! # Numerical covariance of the intrinsic root leaves under permutations

The actual normalized leaf is identified in reindexed boxes by disintegration
on arbitrarily long root intervals.  The time coordinate and its unit ball
do not change, so the normalized measures themselves agree.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma ae_root_free_reindex {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i ≠ j) (μ : Measure (X n))
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∀ᵐ y ∂μ.map (quotientReindex e), ∀ t : ℝ,
      rightAction y (Matrix.SpecialLinearGroup.transvection (e.injective.ne hij) t) = y →
        t = 0 := by
  let Q := (quotientReindexHomeomorph e).toMeasurableEquiv
  change ∀ᵐ y ∂μ.map Q, _
  rw [← Q.map_ae μ]
  change ∀ᵐ x ∂μ, ∀ t : ℝ,
    rightAction (Q x) (Matrix.SpecialLinearGroup.transvection (e.injective.ne hij) t) =
      Q x → t = 0
  filter_upwards [hfree] with x hx
  intro t ht
  apply hx t
  apply Q.injective
  change quotientReindex e (rightAction x _) = quotientReindex e x
  rw [quotientReindex_rightAction, reindex_transvection]
  exact ht

namespace RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

theorem ae_leafMeasure_reindex (A : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      (reindex A e).leafMeasure R (μ.map (quotientReindex e))
        (rootSliceReindexHomeomorph e i j k s) = A.leafMeasure R μ s := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  let S := rootSliceReindexHomeomorph e i j k
  let nu := μ.map (quotientReindex e)
  have hfree' := ae_root_free_reindex e hij μ hfree
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hcov : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
        (reindex B.val e).conditionalKernel nu (S s) = B.val.conditionalKernel μ s := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    exact PrimeDegreePackets.RootBox.base_ae_of_ae A B.val (hinc m B) μ
      (reindex_conditionalKernel B.val e μ)
  have htrans : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
        ((reindex A e).leafMeasure R nu (S s)).restrict B.val.time =
          (anchorNormalize ((reindex B.val e).conditionalKernel nu (S s))
            A.time).restrict B.val.time := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    have H := (reindex A e).ae_leafMeasure_restrict R hAR nu hfree'
      (reindex B.val e) (hinc m B)
    rw [reindex_marginal A e μ] at H
    have H' := ae_of_ae_map S.measurable.aemeasurable H
    filter_upwards [H'] with s hs
    intro hsB
    exact (hs (mem_image_of_mem S hsB)).2
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,
    A.ae_injective_root_slice_of_ae_free μ hfree, hcov, htrans] with s hs hi hc ht
  apply measure_eq_of_restrictionChain (rootLeafWindow R) (rootLeafWindow_mono R)
    (rootLeafWindow_cover R)
  intro m
  obtain ⟨B, hBC, hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
  let B' : C m := ⟨B, hBC⟩
  have he := ht m B' hsB
  rw [hc m B' hsB] at he
  change ((reindex A e).leafMeasure R nu (S s)).restrict B.time =
    (anchorNormalize (B.conditionalKernel μ s) A.time).restrict B.time at he
  rw [rootLongBoxFamily_time hij k R m B hBC] at he
  exact he.trans (hs.2.2.2 m B hBC hsB).symm

lemma ae_basedLeaf_reindex (A : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      (reindex A e).basedLeaf R (μ.map (quotientReindex e))
        (rootReindexCoordinates e i j k z) = A.basedLeaf R μ z := by
  have H := ae_of_ae_map measurable_fst.aemeasurable
    (ae_leafMeasure_reindex A e R hAR μ hfree)
  filter_upwards [H] with z hz
  change basedRealMeasure ((reindex A e).leafMeasure R (μ.map (quotientReindex e))
    (rootSliceReindexHomeomorph e i j k z.1)) z.2 = _
  rw [hz]
  rfl

lemma ae_intrinsicRootLeaf_reindex_restrict (A : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∀ᵐ x ∂μ.restrict A.range,
      intrinsicRootLeaf (e.injective.ne hij) (μ.map (quotientReindex e))
        (quotientReindex e x) = intrinsicRootLeaf hij μ x := by
  apply A.ae_of_coordinate μ
  have HT := (reindex A e).ae_intrinsicRootLeaf_coordinates R hAR
    (μ.map (quotientReindex e)) (ae_root_free_reindex e hij μ hfree)
  rw [reindex_coordinateMeasure A e μ] at HT
  have HT' := ae_of_ae_map (rootReindexCoordinates e i j k).measurable.aemeasurable HT
  filter_upwards [HT', A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
    ae_basedLeaf_reindex A e R hAR μ hfree] with z ht ha hc
  rw [rootReindexCoordinates_param] at ht
  exact ht.trans (hc.trans ha.symm)

end RootBox

/-- Numeric leaf covariance on the actual quotient, not just preservation
of the atomic/non-atomic alternative. -/
theorem ae_intrinsicRootLeaf_reindex {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i ≠ j) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf (e.injective.ne hij) (μ.map (quotientReindex e))
      (quotientReindex e x) = intrinsicRootLeaf hij μ x := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := (ae_restrict_iUnion_iff (μ := μ)
    (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr
    (fun B => RootBox.ae_intrinsicRootLeaf_reindex_restrict B.val.box e
      B.val.radius B.val.time_bound μ hfree)
  simpa only [boundedRootAtlas_iUnion, Measure.restrict_univ] using H

end DukePrimeDegree

end

end OAI
