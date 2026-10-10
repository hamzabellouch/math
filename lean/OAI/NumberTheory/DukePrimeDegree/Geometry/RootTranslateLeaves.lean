import OAI.NumberTheory.DukePrimeDegree.Geometry.RootTranslateBox

namespace OAI

/-!
# Translation covariance of the global normalized root leaf

Long root boxes extend the local disintegration identity to the whole
real root line. Centering cancels the translation, so a preserving root
translation fixes the intrinsic normalized leaf almost everywhere.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets
open PrimeDegreePackets.RootBox
namespace RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

theorem ae_leafMeasure_translate (A : PrimeDegreePackets.RootBox hij k)
    (R S a : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (hAS : (translate A a).time ⊆ rootLeafWindow S 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      (translate A a).leafMeasure S μ s =
        (A.leafMeasure R μ s).map (Homeomorph.addRight a) := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  let f := Homeomorph.addRight a
  let AT := translate A a
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hincT (m : ℕ) (B : C m) : AT.time ⊆ (translate B.val a).time :=
    image_mono (hinc m B)
  have hcov : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse → (translate B.val a).conditionalKernel μ s =
        (B.val.conditionalKernel μ s).map f := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    exact PrimeDegreePackets.RootBox.base_ae_of_ae A B.val (hinc m B) μ
      (translate_conditionalKernel B.val a μ hinv)
  have htrans : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
      (AT.leafMeasure S μ s).restrict (f '' B.val.time) =
        (anchorNormalize ((translate B.val a).conditionalKernel μ s)
          (f '' A.time)).restrict (f '' B.val.time) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    have H := AT.ae_leafMeasure_restrict S hAS μ hfree (translate B.val a) (hincT m B)
    rw [translate_marginal A a μ hinv] at H
    exact H.mono fun s hs hsB => (hs hsB).2
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,
    A.ae_injective_root_slice_of_ae_free μ hfree, hcov, htrans] with s hs hi hc ht
  apply measure_eq_of_restrictionChain (fun m => f '' rootLeafWindow R m)
    (fun p q hpq => image_mono (rootLeafWindow_mono R hpq))
    (by rw [← image_iUnion, rootLeafWindow_cover, image_univ, f.surjective.range_eq])
  intro m
  obtain ⟨B, hBC, hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
  let B' : C m := ⟨B, hBC⟩
  have H := ht m B' hsB
  rw [hc m B' hsB] at H
  have ha : anchorNormalize ((B.conditionalKernel μ s).map f) (f '' A.time) =
      (anchorNormalize (B.conditionalKernel μ s) A.time).map f :=
    anchorNormalize_map_equiv (B.conditionalKernel μ s) f.toMeasurableEquiv A.time
  change (AT.leafMeasure S μ s).restrict (f '' B.time) =
    (anchorNormalize ((B.conditionalKernel μ s).map f) (f '' A.time)).restrict (f '' B.time) at H
  rw [ha] at H
  change (AT.leafMeasure S μ s).restrict (f '' rootLeafWindow R m) =
    ((A.leafMeasure R μ s).map f).restrict (f '' rootLeafWindow R m)
  have hmap (ν : Measure ℝ) (J : Set ℝ) :
      (ν.map f).restrict (f '' J) = (ν.restrict J).map f := by
    exact (f.toMeasurableEquiv.restrict_map ν (f '' J)).trans
      (congrArg (fun T : Set ℝ => (ν.restrict T).map f) (f.injective.preimage_image J))
  rw [hmap, hs.2.2.2 m B hBC hsB]
  rw [hmap] at H
  simpa only [rootLongBoxFamily_time hij k R m B hBC] using H

lemma translate_time_bound (A : PrimeDegreePackets.RootBox hij k) (R a : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0) :
    (translate A a).time ⊆ rootLeafWindow (R + |a|) 0 := by
  rintro _ ⟨t, ht, rfl⟩
  have hh := hAR ht
  simp only [rootLeafWindow, Nat.cast_zero, add_zero, mem_Ioo] at hh ⊢
  change -(R + |a|) < t + a ∧ t + a < R + |a|
  constructor <;> linarith [neg_abs_le a, le_abs_self a]

lemma ae_basedLeaf_translate (A : PrimeDegreePackets.RootBox hij k) (R a : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      (translate A a).basedLeaf (R + |a|) μ (timeTranslation a z) = A.basedLeaf R μ z := by
  have H := ae_of_ae_map measurable_fst.aemeasurable
    (ae_leafMeasure_translate A R (R + |a|) a hAR (translate_time_bound A R a hAR) μ hfree hinv)
  filter_upwards [H] with z hz
  change basedRealMeasure ((translate A a).leafMeasure _ μ z.1) (z.2 + a) = _
  rw [hz]
  exact basedRealMeasure_translate _ _ _

lemma ae_intrinsicRootLeaf_translate_restrict (A : PrimeDegreePackets.RootBox hij k)
    (R a : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ x ∂μ.restrict A.range, intrinsicRootLeaf hij μ
      (rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = intrinsicRootLeaf hij μ x := by
  apply A.ae_of_coordinate μ
  have HT := (translate A a).ae_intrinsicRootLeaf_coordinates
    (R + |a|) (translate_time_bound A R a hAR) μ hfree
  rw [translate_coordinateMeasure A a μ hinv] at HT
  have HT' := ae_of_ae_map (timeTranslation a).measurable.aemeasurable HT
  filter_upwards [HT', A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
    ae_basedLeaf_translate A R a hAR μ hfree hinv] with z ht ha hc
  change intrinsicRootLeaf hij μ (rootQuotientParametrization hij (z.1, z.2 + a)) = _ at ht
  rw [rootQuotientParametrization_add] at ht
  exact ht.trans (hc.trans ha.symm)

end RootBox

/-- A preserving root translation fixes the normalized intrinsic leaf. -/
theorem ae_intrinsicRootLeaf_translate {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (a : ℝ) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ
      (rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = intrinsicRootLeaf hij μ x := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr
    (fun B => RootBox.ae_intrinsicRootLeaf_translate_restrict B.val.box B.val.radius a
      B.val.time_bound μ hfree hinv)
  simpa only [boundedRootAtlas_iUnion, Measure.restrict_univ] using H

end DukePrimeDegree

end

end OAI
