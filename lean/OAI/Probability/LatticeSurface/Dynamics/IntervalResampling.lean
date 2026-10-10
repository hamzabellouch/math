import Mathlib

namespace OAI

open Set MeasureTheory

open scoped ENNReal

namespace IntervalResampling

attribute [local instance] Classical.propDecidable

lemma affine_measure (a b : ℝ) (hab : a<b) :
    ENNReal.ofReal (b-a) • Measure.map (fun t : ℝ => a+(b-a)*t)
      (volume.restrict (Icc (0:ℝ) 1))=volume.restrict (Icc a b) := by
  have hba : 0<b-a := sub_pos.mpr hab
  have he : (fun t : ℝ => a+(b-a)*t) ⁻¹' Icc a b=Icc 0 1 := by
    ext t
    simp only [mem_preimage,mem_Icc]
    constructor
    · intro h
      constructor <;> nlinarith
    · intro h
      constructor <;> nlinarith
  have hm : ENNReal.ofReal (b-a) • Measure.map (fun t : ℝ => a+(b-a)*t) volume=volume := by
    rw [show (fun t : ℝ => a+(b-a)*t)=(fun t : ℝ => a+t) ∘ (fun t : ℝ => (b-a)*t) from rfl,
      ← Measure.map_map (measurable_const_add a) (measurable_const_mul (b-a)),
      ← Measure.map_smul _ (measurable_const_add a).aemeasurable]
    rw [show ENNReal.ofReal (b-a)=ENNReal.ofReal |b-a| by rw [abs_of_pos hba],Real.smul_map_volume_mul_left hba.ne']
    exact (measurePreserving_add_left volume a).map_eq
  have hr := congrArg (fun μ : Measure ℝ => μ.restrict (Icc a b)) hm
  simpa only [Measure.restrict_smul,Measure.restrict_map (show Measurable (fun t : ℝ => a+(b-a)*t) by fun_prop) measurableSet_Icc,he] using hr

lemma affine_integral (a b : ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ENNReal.ofReal (b-a) * (∫⁻ r in Icc (0:ℝ) 1,f (a+(b-a)*r))=∫⁻ t in Icc a b,f t := by
  by_cases hab : a<b
  · have he := congrArg (fun μ : Measure ℝ => ∫⁻ t,f t ∂μ) (affine_measure a b hab)
    simpa only [lintegral_smul_measure,smul_eq_mul,lintegral_map hf (show Measurable (fun r : ℝ => a+(b-a)*r) by fun_prop)] using he
  · have hb : b≤a := le_of_not_gt hab
    have he : volume (Icc a b)=0 := by simp [Real.volume_Icc,ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hb)]
    rw [ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hb),zero_mul,Measure.restrict_eq_zero.mpr he,lintegral_zero_measure]

variable {W : Type*} [MeasurableSpace W] (mW : Measure W)

def region (R : Set W) (l u : W → ℝ) : Set (W×ℝ) := {z | z.1∈R ∧ z.2∈Icc (l z.1) (u z.1)}

lemma measurable_region {R : Set W} (hR : MeasurableSet R) {l u : W → ℝ} (hl : Measurable l) (hu : Measurable u) :
    MeasurableSet (region R l u) := by
  exact (hR.preimage measurable_fst).inter ((measurableSet_le (hl.comp measurable_fst) measurable_snd).inter
    (measurableSet_le measurable_snd (hu.comp measurable_fst)))

lemma slice_integral {R : Set W} (hR : MeasurableSet R) {l u : W → ℝ} (hl : Measurable l) (hu : Measurable u)
    (f : W×ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in region R l u,f z ∂mW.prod volume)=∫⁻ w in R,(∫⁻ t in Icc (l w) (u w),f (w,t)) ∂mW := by
  rw [← lintegral_indicator (measurable_region hR hl hu),lintegral_prod _ ((hf.indicator (measurable_region hR hl hu)).aemeasurable),← lintegral_indicator hR]
  apply lintegral_congr
  intro w
  by_cases hw : w∈R
  · simp only [indicator_of_mem hw]
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro t
    by_cases ht : t∈Icc (l w) (u w)
    · rw [indicator_of_mem (show (w,t)∈region R l u from ⟨hw,ht⟩),indicator_of_mem ht]
    · rw [indicator_of_notMem (show (w,t)∉region R l u from fun h => ht h.2),indicator_of_notMem ht]
  · simp only [indicator_of_notMem hw]
    have he : ∀ t,(region R l u).indicator f (w,t)=0 := by intro t;simp [region,hw]
    simp only [he,lintegral_zero]

lemma invariant {R : Set W} (hR : MeasurableSet R) {l u : W → ℝ} (hl : Measurable l) (hu : Measurable u) :
    Measure.map (fun z : (W×ℝ)×ℝ => (z.1.1,l z.1.1+(u z.1.1-l z.1.1)*z.2))
      (((mW.prod volume).restrict (region R l u)).prod (volume.restrict (Icc (0:ℝ) 1)))=
      (mW.prod volume).restrict (region R l u) := by
  let T : (W×ℝ)×ℝ → W×ℝ := fun z => (z.1.1,l z.1.1+(u z.1.1-l z.1.1)*z.2)
  have hT : Measurable T := by dsimp [T];fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hT,lintegral_prod (fun z => f (T z)) ((hf.comp hT).aemeasurable)]
  have hm : Measurable (fun z : W×ℝ => ∫⁻ r in Icc (0:ℝ) 1,f (T (z,r))) :=
    (hf.comp hT).lintegral_prod_right'
  rw [slice_integral mW hR hl hu _ hm,slice_integral mW hR hl hu f hf]
  apply lintegral_congr
  intro w
  dsimp [T]
  rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,mul_comm]
  exact affine_integral (l w) (u w) (fun t => f (w,t)) (hf.comp (measurable_const.prodMk measurable_id))

end IntervalResampling

end OAI
