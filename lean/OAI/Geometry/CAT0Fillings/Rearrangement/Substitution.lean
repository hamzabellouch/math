import Mathlib
import OAI.Geometry.CAT0Fillings.Rearrangement.Inverse

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

lemma lipschitz_real_image_null {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {s : Set ℝ} (hs : volume s = 0) : volume (f '' s) = 0 := by
  have h := hf.hausdorffMeasure_image_le (d := 1) (by norm_num) s
  rw [MeasureTheory.hausdorffMeasure_real,hs,mul_zero] at h
  exact le_antisymm h zero_le

lemma lipschitz_real_image_ae_subset {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {s t : Set ℝ} (hts : t ⊆ s) (hst : s =ᵐ[volume] t) :
    f '' s =ᵐ[volume] f '' t := by
  apply ae_eq_set.mpr
  constructor
  · have hsub : f '' s \ f '' t ⊆ f '' (s \ t) := by
      rintro y ⟨⟨x,hx,rfl⟩,hy⟩
      exact ⟨x,⟨hx,fun h => hy ⟨x,h,rfl⟩⟩,rfl⟩
    exact measure_mono_null hsub (lipschitz_real_image_null hf (ae_eq_set.mp hst).1)
  · rw [sdiff_eq_empty.mpr (image_mono hts),measure_empty]

lemma lintegral_image_antitone_lipschitz {h : ℝ → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) {s : Set ℝ} (hs : MeasurableSet s)
    (hanti : AntitoneOn h s) (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in h '' s, g t = ∫⁻ r in s, ENNReal.ofReal (-deriv h r)*g (h r) := by
  let D : Set ℝ := {r | r ∈ s ∧ DifferentiableAt ℝ h r}
  have hD : D =ᵐ[volume] s := by
    filter_upwards [hh.ae_differentiableAt (μ := volume)] with r hr
    change (r ∈ s ∧ DifferentiableAt ℝ h r) = (r ∈ s)
    exact propext ⟨And.left,fun hm => ⟨hm,hr⟩⟩
  obtain ⟨d,hds,hdm,hde⟩ :=
    (hs.nullMeasurableSet.congr hD.symm).exists_measurable_subset_ae_eq
  have hsub : d ⊆ s := fun r hr => (hds hr).1
  have hder : ∀ r ∈ d, HasDerivWithinAt h (deriv h r) d r :=
    fun r hr => (hds hr).2.hasDerivAt.hasDerivWithinAt
  have heq : d =ᵐ[volume] s := hde.trans hD
  calc
    _ = ∫⁻ t in h '' d, g t :=
      setLIntegral_congr (lipschitz_real_image_ae_subset hh hsub heq.symm)
    _ = ∫⁻ r in d, ENNReal.ofReal (-deriv h r)*g (h r) :=
      lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn hdm hder (hanti.mono hsub) g
    _ = _ := setLIntegral_congr heq

lemma lintegral_antitone_interval {h : ℝ → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) {a b : ℝ} (hab : a ≤ b)
    (hanti : AntitoneOn h (Icc a b)) (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in Icc (h b) (h a), g t =
      ∫⁻ r in Icc a b, ENNReal.ofReal (-deriv h r)*g (h r) := by
  rw [←hh.continuous.continuousOn.image_Icc_of_antitoneOn hab hanti]
  exact lintegral_image_antitone_lipschitz hh measurableSet_Icc hanti g

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

lemma ae_inverse_derivative {R : ℝ → ℝ} {U c : ℝ}
    (hU : 0 ≤ U) (hc : 0 < c) (hR : Antitone R)
    (hD : ∀ s t : ℝ, 0 < s → s < t → t < U → c*(t-s) ≤ R s-R t) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 U),
      HasDerivAt R (deriv R t) t ∧
      HasDerivAt (radialInverse R U) (deriv R t)⁻¹ (R t) ∧ deriv R t ≠ 0 := by
  let h := radialInverse R U
  have hh := radialInverse_lipschitz hU hc (hR.antitoneOn _) hD
  let N : Set ℝ := {r | ¬ DifferentiableAt ℝ h r}
  have hN : volume N = 0 := by
    exact (ae_iff.mp (hh.ae_differentiableAt (μ := volume)))
  have hI : volume (h '' N) = 0 := lipschitz_real_image_null hh hN
  have ha : ∀ᵐ t ∂volume, t ∉ h '' N := by
    simpa only [ae_iff,not_not,mem_ofPred_eq, ofPred_mem_eq] using hI
  filter_upwards [ae_restrict_of_ae ha, ae_restrict_of_ae hR.neg.ae_differentiableAt,
    (ae_restrict_mem measurableSet_Ioo : ∀ᵐ t ∂volume.restrict (Ioo 0 U), t ∈ Ioo 0 U)]
      with t ht hRt htI
  have hRt : DifferentiableAt ℝ R t := by simpa using hRt.neg
  have he : h (R t) = t := radialInverse_radius_identity hc (hR.antitoneOn _) htI.1 htI.2 hD
  have hht : DifferentiableAt ℝ h (R t) := by
    by_contra hn
    exact ht ⟨R t,hn,he⟩
  have hid : (fun s : ℝ => s) =ᶠ[𝓝 t] (fun s => h (R s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds htI] with s hs
    exact (radialInverse_radius_identity hc (hR.antitoneOn _) hs.1 hs.2 hD).symm
  have hcomp := hht.hasDerivAt.comp t hRt.hasDerivAt
  have hone : deriv h (R t)*deriv R t = 1 :=
    (hcomp.congr_of_eventuallyEq hid).unique (hasDerivAt_id t)
  have hn : deriv R t ≠ 0 := by intro hn; simp [hn] at hone
  have hform : deriv h (R t) = (deriv R t)⁻¹ := by
    apply (mul_left_inj' hn).mp
    rw [hone,inv_mul_cancel₀ hn]
  exact ⟨hRt.hasDerivAt,by rw [←hform]; exact hht.hasDerivAt,hn⟩

end CAT0Fillings.Rearrangement
end

end OAI
