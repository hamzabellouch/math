import Mathlib
import OAI.Analysis.AffineBernstein.SphereIsometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral
open scoped Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma product_vertical_hyperplane_volume_zero :
    volume {x : WithLp 2 (F × ℝ) | (WithLp.ofLp x).2 = 0} = 0 := by
  have he : {x : WithLp 2 (F × ℝ) | (WithLp.ofLp x).2 = 0} =
      WithLp.ofLp ⁻¹' ((univ : Set F) ×ˢ ({0} : Set ℝ)) := by ext x; simp
  rw [he,(WithLp.volume_preserving_ofLp F ℝ).measure_preimage
    (MeasurableSet.univ.prod (measurableSet_singleton 0)).nullMeasurableSet]
  change ((volume : Measure F).prod (volume : Measure ℝ)) (univ ×ˢ {0}) = 0
  rw [Measure.prod_prod,measure_singleton,mul_zero]

/- The equator is null for the actual Haar-induced sphere measure. -/
lemma product_sphere_equator_null :
    (volume : Measure (WithLp 2 (F × ℝ))).toSphere
      {e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1 | (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 = 0} = 0 := by
  have hs : MeasurableSet {e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1 |
      (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 = 0} := by
    exact (isClosed_eq (by fun_prop) continuous_const).measurableSet
  rw [Measure.toSphere_apply' _ hs]
  have hh : volume (Ioo (0:ℝ) 1 • (Subtype.val ''
      {e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1 |
        (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 = 0})) = 0 := by
    apply measure_mono_null _ product_vertical_hyperplane_volume_zero
    rintro x ⟨t,ht,y,⟨e,he,rfl⟩,rfl⟩
    simpa using congrArg (fun a : ℝ => t*a) he
  rw [hh,mul_zero]

/- Full-sphere nonnegative integration is the sum of the two open hemispheres.
The codimension-one null set is proved from product volume, including dim F=0. -/
theorem product_sphere_lintegral_split (g : WithLp 2 (F × ℝ) → ℝ≥0∞)
    (hg : Measurable g) :
    (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1, g e ∂volume.toSphere) =
      (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
        if 0 < (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 then g e else 0 ∂volume.toSphere) +
      (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
        if (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 < 0 then g e else 0 ∂volume.toSphere) := by
  have hne : ∀ᵐ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1 ∂volume.toSphere,
      (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 ≠ 0 := by
    rw [ae_iff]
    simpa using (product_sphere_equator_null (F:=F))
  have hf : Measurable (fun e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1 =>
      if 0 < (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 then g e else 0) := by
    exact (hg.comp measurable_subtype_coe).ite
      ((isOpen_lt continuous_const (by fun_prop)).measurableSet) measurable_const
  rw [← lintegral_add_left hf]
  apply lintegral_congr_ae
  filter_upwards [hne] with e he
  rcases lt_or_gt_of_ne he with h | h
  · simp only [ite_eq_left h,ite_eq_right (not_lt_of_ge h.le),zero_add]
  · simp only [ite_eq_left h,ite_eq_right (not_lt_of_ge h.le),add_zero]

/- Antipodal transport identifies the negative hemisphere with a positive one. -/
theorem product_sphere_negative_lintegral (g : WithLp 2 (F × ℝ) → ℝ≥0∞) :
    (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
      if (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 < 0 then g e else 0 ∂volume.toSphere) =
    (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
      if 0 < (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 then g (- (e:WithLp 2 (F × ℝ)))
      else 0 ∂volume.toSphere) := by
  have h := (linearIsometrySphere_measurePreserving
    (LinearIsometryEquiv.neg ℝ (E:=WithLp 2 (F × ℝ)))).lintegral_comp_emb
      (linearIsometrySphereHomeomorph
        (LinearIsometryEquiv.neg ℝ (E:=WithLp 2 (F × ℝ)))).measurableEmbedding
      (fun e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1 =>
        if (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 < 0 then g e else 0)
  symm
  convert h using 1
  apply lintegral_congr
  intro e
  simp
  rfl

end AffineBernstein
end

end OAI
