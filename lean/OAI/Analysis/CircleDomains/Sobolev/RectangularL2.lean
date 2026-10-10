import OAI.Analysis.CircleDomains.Uniformization.ComplexRectangleLimit
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Finite rectangle integration is continuous for the actual strong L2
residuals. The coordinate and almost-everywhere bridges retain the full
closed rectangle required by Morera. -/
open Set Function Filter MeasureTheory Complex
open scoped Topology Interval ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma tendsto_complex_setIntegral_L2 {q : ℕ → PlaneL2}
    (hq : Tendsto q atTop (𝓝 0)) {A : Set ℂ} (hA : MeasurableSet A)
    (hfin : volume A ≠ ∞) :
    Tendsto (fun n => ∫z in A,q n z) atTop (𝓝 0) := by
  have h := tendsto_const_nhds.inner (𝕜 := ℂ) hq
    (x := indicatorConstLp 2 hA hfin (1 : ℂ))
  simpa only [L2.inner_indicatorConstLp_one,inner_zero_right] using h

lemma doubleSetIntegral_eq_complex_integral {q : ℂ → ℂ} (a b c d : ℝ)
    (hq : IntegrableOn q (Ioc a b ×ℂ Ioc c d)) :
    (∫x in Ioc a b,∫y in Ioc c d,q (x+y*I))=
      ∫z in Ioc a b ×ℂ Ioc c d,q z := by
  let e := Complex.measurableEquivRealProd.symm
  have he := Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  have hpre : e ⁻¹' (Ioc a b ×ℂ Ioc c d)=Ioc a b ×ˢ Ioc c d := by
    ext p
    rfl
  have hi := (he.integrableOn_comp_preimage e.measurableEmbedding).mpr hq
  rw [hpre] at hi
  rw [←he.setIntegral_preimage_emb e.measurableEmbedding q, hpre,Measure.volume_eq_prod,←Measure.prod_restrict]
  rw [IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict] at hi
  have hprod := integral_prod (q ∘ e) hi
  simp only [Function.comp_apply] at hprod
  rw [hprod]
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  exact Complex.re_add_im (e (x,y))

lemma tendsto_doubleSetIntegral_L2 {q : ℕ → PlaneL2}
    (hq : Tendsto q atTop (𝓝 0)) (a b c d : ℝ) :
    Tendsto (fun n => ∫x in Ioc a b,∫y in Ioc c d,q n (x+y*I)) atTop (𝓝 0) := by
  have hm : MeasurableSet (Ioc a b ×ℂ Ioc c d) :=
    (measurableSet_Ioc.preimage Complex.continuous_re.measurable).inter
      (measurableSet_Ioc.preimage Complex.continuous_im.measurable)
  have hf : volume (Ioc a b ×ℂ Ioc c d) ≠ ∞ := by
    apply ne_of_lt
    exact (measure_mono (show Ioc a b ×ℂ Ioc c d⊆Icc a b ×ℂ Icc c d from
      fun z hz => ⟨⟨hz.1.1.le,hz.1.2⟩,⟨hz.2.1.le,hz.2.2⟩⟩)).trans_lt
        (isCompact_Icc.reProdIm isCompact_Icc).measure_lt_top
  have hi (n : ℕ) := integrableOn_Lp_of_measure_ne_top (q n) (by norm_num) hf
  simpa only [doubleSetIntegral_eq_complex_integral a b c d (hi _)] using
    tendsto_complex_setIntegral_L2 hq hm hf

lemma tendsto_doubleIntervalIntegral_L2 {q : ℕ → PlaneL2}
    (hq : Tendsto q atTop (𝓝 0)) (a b c d : ℝ) :
    Tendsto (fun n => ∫x in a..b,∫y in c..d,q n (x+y*I)) atTop (𝓝 0) := by
  by_cases hab : a≤b <;> by_cases hcd : c≤d
  · simpa only [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hcd] using
      tendsto_doubleSetIntegral_L2 hq a b c d
  · simpa only [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_ge (le_of_not_ge hcd),
      integral_neg,neg_zero] using (tendsto_doubleSetIntegral_L2 hq a b d c).neg
  · simpa only [intervalIntegral.integral_of_ge (le_of_not_ge hab),intervalIntegral.integral_of_le hcd,
      neg_zero] using (tendsto_doubleSetIntegral_L2 hq b a c d).neg
  · simpa only [intervalIntegral.integral_of_ge (le_of_not_ge hab),
      intervalIntegral.integral_of_ge (le_of_not_ge hcd),integral_neg,neg_neg] using
      tendsto_doubleSetIntegral_L2 hq b a d c

lemma doubleIntervalIntegral_congr_ae {f g : ℂ → ℂ} (z w : ℂ)
    (h : ∀ᵐp ∂volume,p∈Rectangle z w → f p=g p) :
    (∫x in z.re..w.re,∫y in z.im..w.im,f (x+y*I))=
      ∫x in z.re..w.re,∫y in z.im..w.im,g (x+y*I) := by
  have he := Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  have hp := MeasureTheory.Measure.ae_ae_of_ae_prod (he.quasiMeasurePreserving.ae h)
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hp] with x hx hxI
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hx] with y hy hyI
  have heq : Complex.measurableEquivRealProd.symm (x,y)=(x:ℂ)+y*I := by
    exact (Complex.re_add_im _).symm
  rw [←heq]
  apply hy
  change x∈uIcc z.re w.re ∧ y∈uIcc z.im w.im
  exact ⟨uIoc_subset_uIcc hxI,uIoc_subset_uIcc hyI⟩

end CircleDomainRigidity

end

end OAI
