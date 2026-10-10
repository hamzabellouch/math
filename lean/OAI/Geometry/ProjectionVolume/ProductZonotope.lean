import OAI.Geometry.ProjectionVolume.SimplexZonotope
import OAI.Geometry.ProjectionVolume.ProductVolume

namespace OAI

universe uE uF

open Set MeasureTheory
open scoped Pointwise RealInnerProductSpace

namespace Paper092

noncomputable def productZonotope : Set (Euclidean 20) :=
  splitBlocks ⁻¹'
    (((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10) ×ˢ
      ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10))

theorem productZonotope_isCompact : IsCompact productZonotope := by
  unfold productZonotope
  have h : IsCompact ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10) :=
    IsCompact.smul _ (simplexZonotope_isCompact 10)
  exact splitBlocks.toHomeomorph.isCompact_preimage.mpr (h.prod h)

theorem productZonotope_nonempty : productZonotope.Nonempty := by
  unfold productZonotope
  have h : ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10).Nonempty :=
    (simplexZonotope_nonempty 10).smul_set
  exact (h.prod h).preimage splitBlocks.surjective

theorem productZonotope_convex : Convex ℝ productZonotope := by
  unfold productZonotope
  have h : Convex ℝ ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10) :=
    (simplexZonotope_convex 10).smul _
  exact (h.prod h).linear_preimage splitBlocks.toLinearMap

theorem inner_splitBlocks_sum (u v : Euclidean 20) :
    inner ℝ u v = inner ℝ (firstBlock u) (firstBlock v) +
      inner ℝ (secondBlock u) (secondBlock v) := by
  exact Fin.sum_univ_add (fun i : Fin (10 + 10) => inner ℝ (u i) (v i))

theorem support_preimage_equiv {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) (K : Set F)
    (f : F →L[ℝ] ℝ) :
    SupportGeometry.support (e ⁻¹' K) (f.comp e.toContinuousLinearMap) =
      SupportGeometry.support K f := by
  unfold SupportGeometry.support
  change sSup ((f ∘ e) '' (e ⁻¹' K)) = _
  rw [image_comp f e, image_preimage_eq K e.surjective]

theorem productZonotope_support_factor (u : Euclidean 20) :
    SupportGeometry.support productZonotope (innerSL ℝ u) =
      (1 / (Nat.factorial 10 : ℝ)) *
        (SupportGeometry.support (simplexZonotope 10) (innerSL ℝ (firstBlock u)) +
          SupportGeometry.support (simplexZonotope 10) (innerSL ℝ (secondBlock u))) := by
  have hlin : innerSL ℝ u =
      ((innerSL ℝ (firstBlock u)).coprod (innerSL ℝ (secondBlock u))).comp
        splitBlocks.toContinuousLinearMap := by
    ext y
    exact inner_splitBlocks_sum u y
  have hc : IsCompact ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10) :=
    IsCompact.smul _ (simplexZonotope_isCompact 10)
  have hn : ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10).Nonempty :=
    (simplexZonotope_nonempty 10).smul_set
  rw [hlin, productZonotope, support_preimage_equiv,
    SupportGeometry.support_prod hc hn hc hn,
    SupportGeometry.support_smul _ _ (by positivity),
    SupportGeometry.support_smul _ _ (by positivity), mul_add]

theorem productZonotope_support (u : Euclidean 20) :
    SupportGeometry.support productZonotope (innerSL ℝ u) =
      ((∑ i : Fin 10, |firstBlock u i|) + |∑ i : Fin 10, firstBlock u i| +
        (∑ i : Fin 10, |secondBlock u i|) + |∑ i : Fin 10, secondBlock u i|) /
          (2 * (Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ)) := by
  rw [productZonotope_support_factor, simplexZonotope_support, simplexZonotope_support]
  change (1 / (Nat.factorial 10 : ℝ)) *
    (((∑ i : Fin 10, |firstBlock u i|) + |∑ i : Fin 10, firstBlock u i|) /
        (2 * (Nat.factorial 9 : ℝ)) +
      ((∑ i : Fin 10, |secondBlock u i|) + |∑ i : Fin 10, secondBlock u i|) /
        (2 * (Nat.factorial 9 : ℝ))) = _
  ring

theorem productZonotope_volume_product :
    volume productZonotope =
      volume ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10) *
      volume ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10) := by
  have hc : IsCompact ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10) :=
    IsCompact.smul _ (simplexZonotope_isCompact 10)
  rw [productZonotope, splitBlocks_measurePreserving.measure_preimage
    (hc.prod hc).measurableSet.nullMeasurableSet]
  exact Measure.prod_prod _ _

theorem productZonotope_volume_real :
    (volume productZonotope).toReal =
      (121 : ℝ) / ((Nat.factorial 9 : ℝ) ^ 20 * (Nat.factorial 10 : ℝ) ^ 20) := by
  have hscaled :
      (volume ((1 / (Nat.factorial 10 : ℝ)) • simplexZonotope 10)).toReal =
        (1 / (Nat.factorial 10 : ℝ)) ^ 10 * (11 / (Nat.factorial 9 : ℝ) ^ 10) := by
    rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_pow, abs_of_nonneg (by positivity),
      simplexZonotope_volume 10 (by norm_num)]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
  rw [productZonotope_volume_product, ENNReal.toReal_mul, hscaled]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem productZonotope_volume :
    volume productZonotope = ENNReal.ofReal
      ((121 : ℝ) / ((Nat.factorial 9 : ℝ) ^ 20 * (Nat.factorial 10 : ℝ) ^ 20)) := by
  rw [← productZonotope_volume_real, ENNReal.ofReal_toReal productZonotope_isCompact.measure_lt_top.ne]

end Paper092

end OAI
