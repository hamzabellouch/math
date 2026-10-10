import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedWindow
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactShiftedObservation

namespace OAI

/-! Actual bounded Fourier tests on finite translated-cusp windows. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaShiftedFourierWeight (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (p : CubicThetaPoint) : ℂ :=
  W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaShiftedRowFrequency h)):ℂ)

lemma cubicThetaShiftedFourierWeight_continuous (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    Continuous (cubicThetaShiftedFourierWeight h W) := by
  have hc : Continuous (fun p : CubicThetaPoint =>
      Real.fourierChar (tracePair p.val.1 (cubicThetaShiftedRowFrequency h))) :=
    Real.continuous_fourierChar.comp (by unfold tracePair; fun_prop)
  exact (W.continuous.comp (continuous_snd.comp continuous_subtype_val)).mul
    (continuous_subtype_val.comp hc)

lemma cubicThetaShiftedWindowWeight_memLp (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K) :
    MemLp ((cubicThetaShiftedWindow a d).indicator (cubicThetaShiftedFourierWeight h W))
      2 (cubicThetaPointMeasure.restrict K) := by
  classical
  let : IsFiniteMeasure (cubicThetaPointMeasure.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C,hC⟩ := W.hasCompactSupport.exists_bound_of_continuousOn W.continuous.continuousOn
  apply MemLp.of_bound
    ((cubicThetaShiftedFourierWeight_continuous h W).aestronglyMeasurable.indicator
      (cubicThetaShiftedWindow_measurable a d)) (max C 0)
  apply Filter.Eventually.of_forall
  intro p
  by_cases hp : p∈cubicThetaShiftedWindow a d
  · rw [indicator_of_mem hp,cubicThetaShiftedFourierWeight,norm_mul,Circle.norm_coe,mul_one]
    by_cases hv : p.val.2∈tsupport W
    · exact (hC _ hv).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hv,norm_zero]
      exact le_max_right _ _
  · rw [indicator_of_notMem hp,norm_zero]
    exact le_max_right _ _

def cubicThetaShiftedWindowTest (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K) :
    Lp ℂ 2 (cubicThetaPointMeasure.restrict K) :=
  (cubicThetaShiftedWindowWeight_memLp h W a d hK).toLp _

lemma cubicThetaShiftedWindowTest_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K)
    (R : Lp ℂ 2 (cubicThetaPointMeasure.restrict K)) (f : CubicThetaPoint → ℂ)
    (hf : R=ᵐ[cubicThetaPointMeasure.restrict K] f) :
    IntegrableOn (fun p => star (cubicThetaShiftedFourierWeight h W p)*f p)
      (cubicThetaShiftedWindow a d) cubicThetaPointMeasure := by
  classical
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaShiftedWindowTest h W a d hK) R
  have he : Integrable ((cubicThetaShiftedWindow a d).indicator
      (fun p => star (cubicThetaShiftedFourierWeight h W p)*f p))
      (cubicThetaPointMeasure.restrict K) := by
    apply hi.congr
    filter_upwards [(cubicThetaShiftedWindowWeight_memLp h W a d hK).coeFn_toLp,hf]
      with p hp hfp
    change inner ℂ (((cubicThetaShiftedWindowWeight_memLp h W a d hK).toLp _) p) _=_
    rw [hp,hfp,RCLike.inner_apply]
    simp only [starRingEnd_apply]
    by_cases hm : p∈cubicThetaShiftedWindow a d
    · simp only [indicator_of_mem hm]; ring
    · simp only [indicator_of_notMem hm,star_zero,mul_zero]
  rw [integrable_indicator_iff (cubicThetaShiftedWindow_measurable a d)] at he
  simpa only [IntegrableOn,Measure.restrict_restrict (cubicThetaShiftedWindow_measurable a d),
    inter_eq_left.mpr hSK] using he

lemma cubicThetaShiftedWindowTest_pairing (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K)
    (R : Lp ℂ 2 (cubicThetaPointMeasure.restrict K)) (f : CubicThetaPoint → ℂ)
    (hf : R=ᵐ[cubicThetaPointMeasure.restrict K] f) :
    inner ℂ (cubicThetaShiftedWindowTest h W a d hK) R=
      ∫ p in cubicThetaShiftedWindow a d,
        star (cubicThetaShiftedFourierWeight h W p)*f p ∂cubicThetaPointMeasure := by
  classical
  rw [L2.inner_def]
  calc
    _ = ∫ p in K,(cubicThetaShiftedWindow a d).indicator
        (fun p => star (cubicThetaShiftedFourierWeight h W p)*f p) p
        ∂cubicThetaPointMeasure := by
      apply integral_congr_ae
      filter_upwards [(cubicThetaShiftedWindowWeight_memLp h W a d hK).coeFn_toLp,hf]
        with p hp hfp
      change inner ℂ (((cubicThetaShiftedWindowWeight_memLp h W a d hK).toLp _) p) _=_
      rw [hp,hfp,RCLike.inner_apply]
      simp only [starRingEnd_apply]
      by_cases hm : p∈cubicThetaShiftedWindow a d
      · simp only [indicator_of_mem hm]; ring
      · simp only [indicator_of_notMem hm,star_zero,mul_zero]
    _ = _ := by
      rw [setIntegral_indicator (cubicThetaShiftedWindow_measurable a d),
        inter_eq_right.mpr hSK]

def cubicThetaShiftedWindowObservation (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K) (s : ℂ) : ℂ :=
  cubicThetaCompactShiftedObservation b hK (cubicThetaShiftedWindowTest h W a d hK) s

lemma cubicThetaShiftedWindowObservation_meromorphic (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K) {s : ℂ} (hs : 1<s.re) :
    MeromorphicAt (cubicThetaShiftedWindowObservation b h W a d hK) s :=
  cubicThetaCompactShiftedObservation_meromorphic b hK _ hs

lemma cubicThetaShiftedWindowObservation_right (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K) (hhigh : ∀ p∈K,1<p.val.2)
    {s : ℂ} (hs : 3<s.re) :
    cubicThetaShiftedWindowObservation b h W a d hK s=
      cubicThetaResidueScale*∫ p in cubicThetaShiftedWindow a d,
        star (cubicThetaShiftedFourierWeight h W p)*cubicThetaEisenstein
          ((cubicThetaInversion 1 p.val).1+b,(cubicThetaInversion 1 p.val).2) s
        ∂cubicThetaPointMeasure := by
  unfold cubicThetaShiftedWindowObservation cubicThetaCompactShiftedObservation
  rw [cubicThetaShiftedWindowTest_pairing h W a d hK hSK _ _
    (cubicThetaCompactShiftedFamily_right b hK hhigh hs),←integral_const_mul]
  congr 1
  ext p
  ring

lemma cubicThetaShiftedWindowObservation_residue (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K) :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaShiftedWindowObservation b h W a d hK s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (∫ p in cubicThetaShiftedWindow a d,
        star (cubicThetaShiftedFourierWeight h W p)*
          cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
            (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)
        ∂cubicThetaPointMeasure)) := by
  have ht := ((innerSL ℂ (cubicThetaShiftedWindowTest h W a d hK)).continuous.tendsto _).comp
    (cubicThetaCompactShiftedFamily_residue b hK)
  simp only [Function.comp_def,innerSL_apply_apply,inner_smul_right] at ht
  rw [cubicThetaShiftedWindowTest_pairing h W a d hK hSK _ _
    (cubicThetaCompactShiftedResidue_model b hK)] at ht
  simpa only [Function.comp_def,innerSL_apply_apply,inner_smul_right,
    cubicThetaShiftedWindowObservation,cubicThetaCompactShiftedObservation] using ht

end CubicFirstMoment

end

end OAI
