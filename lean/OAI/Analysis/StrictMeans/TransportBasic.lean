import OAI.Analysis.StrictMeans.LawDensity

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

abbrev upperArea : Measure UpperHalfPlane := (volume : Measure ℂ).comap UpperHalfPlane.coe

lemma coe_upperArea_preserving : MeasurePreserving UpperHalfPlane.coe upperArea
    (volume.restrict {z : ℂ | 0 < z.im}) := by
  refine ⟨UpperHalfPlane.measurable_coe,?_⟩
  rw [UpperHalfPlane.measurableEmbedding_coe.map_comap,UpperHalfPlane.range_coe]

lemma upperArea_lintegral {h : UpperHalfPlane → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ z, h z ∂upperArea) = ∫⁻ z in {z : ℂ | 0 < z.im}, h (halfPlaneProjection z) := by
  have he := coe_upperArea_preserving.lintegral_comp (hh.comp measurable_halfPlaneProjection)
  have hp (z : UpperHalfPlane) : halfPlaneProjection z = z := by
    rw [halfPlaneProjection_of_pos z.im_pos]
  simpa only [Function.comp_apply,hp] using he

lemma upper_source_area_formula {β k : ℝ} (hk : k ≠ 0) (f : DiskFamily) (positive : Bool)
    {h : UpperHalfPlane → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ z, h z * sourceMassDensity β k f positive z ∂upperArea) =
      ∫⁻ ξ, fiberSum (criticalMap k (halfPlaneFunction f)) (signedJacobianLocus k f positive)
        (fun z => h (halfPlaneProjection z) * unsignedTargetWeight β f (halfPlaneProjection z)) ξ := by
  have hm : Measurable (fun z => h z * sourceMassDensity β k f positive z) :=
    hh.mul ((continuous_sourceMassDensity β k positive).measurable.comp
      (measurable_const.prodMk measurable_id))
  rw [upperArea_lintegral hm]
  exact source_area_formula hk f positive (hh.comp measurable_halfPlaneProjection)

lemma unsignedTargetWeight_height {β k : ℝ} (hk : k ≠ 0) (hβ : 3*(k-1)=β-1)
    (f : DiskFamily) (z : UpperHalfPlane) :
    unsignedTargetWeight β f z = ENNReal.ofReal ((criticalHeight k (halfPlaneFunction f) z / k)^3) := by
  unfold unsignedTargetWeight criticalHeight halfPlaneQ
  congr 1
  have hc : k*z.im^(k-1)*‖(deriv (halfPlaneFunction f) z)⁻¹‖/k =
      z.im^(k-1)*‖(deriv (halfPlaneFunction f) z)⁻¹‖ := by field_simp
  simp only [UpperHalfPlane.coe_im]
  rw [hc,mul_pow,← Real.rpow_mul_natCast z.im_pos.le (k-1) 3]
  norm_num only [Nat.cast_ofNat]
  rw [mul_comm (k-1) (3:ℝ),hβ]

lemma partnerRatio_weight {β k : ℝ} (hk : 0 < k) (hβ : 3*(k-1)=β-1)
    (f : DiskFamily) (z : UpperHalfPlane) (hz : (f,z) ∈ sourcePairingDomain k) :
    ENNReal.ofReal (partnerRatio k (f,z)) * unsignedTargetWeight β f z =
      unsignedTargetWeight β f (sourcePartner k (f,z)) := by
  rw [unsignedTargetWeight_height hk.ne' hβ,unsignedTargetWeight_height hk.ne' hβ,
    ← ENNReal.ofReal_mul (partnerRatio_nonneg hk _)]
  congr 1
  rw [partnerRatio,ite_eq_left hz]
  have hv := (criticalHeight_pos hk z.im_pos (halfPlaneFunction_deriv_ne_zero f z.im_pos)).ne'
  field_simp

lemma fiberSum_indicator {X Y : Type*} (G : X → Y) (s t : Set X) (h : X → ℝ≥0∞) (ξ : Y) :
    fiberSum G s (t.indicator h) ξ = fiberSum G (s ∩ t) h ξ := by
  classical
  unfold fiberSum
  rw [tsum_subtype,tsum_subtype]
  apply tsum_congr
  intro z
  by_cases hs : z∈s <;> by_cases ht : z∈t <;> by_cases hg : G z=ξ <;>
    simp [hs,ht,hg]

lemma fiberSum_congr {X Y : Type*} {G : X → Y} {s : Set X} {h q : X → ℝ≥0∞}
    (ξ : Y) (he : ∀ z∈s, G z=ξ → h z=q z) : fiberSum G s h ξ=fiberSum G s q ξ := by
  unfold fiberSum
  apply tsum_congr
  intro z
  exact he z z.2.1 z.2.2

lemma sourcePartner_injectiveOn {k : ℝ} (hk : 0 < k) (f : DiskFamily) :
    InjOn (fun z => sourcePartner k (f,z)) {z | (f,z) ∈ sourcePairingDomain k} := by
  intro z hz w hw he
  apply sourcePartner_injOn_fiber hk f hz hw _ he
  rw [← (sourcePartner_spec k hz).2.2.2.1,← (sourcePartner_spec k hw).2.2.2.1]
  exact congrArg (fun w : UpperHalfPlane => criticalMap k (halfPlaneFunction f) w) he

end
end StrictInverseFirstPower

end

end OAI
