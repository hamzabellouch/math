import OAI.NumberTheory.Jacobsthal.Estimates.BoundedLossTerms

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings

theorem weighted_threshold_swap {P W T : ℝ → ℝ}
    (hP : Measurable P) (hW : Measurable W) (hT : Measurable T)
    (a Y b CP CW : ℝ) (hCP : 0 ≤ CP) (hCW : 0 ≤ CW)
    (hPb : ∀ y ∈ Icc a Y,|P y| ≤ CP)
    (hWb : ∀ t ∈ Icc (1:ℝ) b,|W t| ≤ CW)
    (hTb : ∀ t ∈ Icc (1:ℝ) b,a ≤ T t ∧ T t ≤ Y) :
    (∫ y in Icc a Y,P y*(∫ t in Icc (1:ℝ) b,if y<T t then W t else 0))=
      ∫ t in Icc (1:ℝ) b,W t*(∫ y : ℝ in a..T t,P y) := by
  classical
  let G : ℝ×ℝ → ℝ := fun p => if p.1<T p.2 then P p.1*W p.2 else 0
  have hG : Measurable G := Measurable.ite
    (measurableSet_lt measurable_fst (hT.comp measurable_snd))
    ((hP.comp measurable_fst).mul (hW.comp measurable_snd)) measurable_const
  have hb : ∀ y ∈ Icc a Y,∀ t ∈ Icc (1:ℝ) b,|G (y,t)| ≤ CP*CW := by
    intro y hy t ht
    dsimp only [G]
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul (hPb y hy) (hWb t ht) (abs_nonneg _) hCP
    · simpa only [abs_zero] using mul_nonneg hCP hCW
  have hs := bounded_rectangle_swap hG a Y 1 b (CP*CW) hb
  have hleft (y : ℝ) : (∫ t in Icc (1:ℝ) b,G (y,t))=
      P y*(∫ t in Icc (1:ℝ) b,if y<T t then W t else 0) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [G]
    split_ifs <;> simp
  have hright (t : ℝ) (ht : t ∈ Icc (1:ℝ) b) :
      (∫ y in Icc a Y,G (y,t))=W t*(∫ y : ℝ in a..T t,P y) := by
    have hset : Icc a Y ∩ Iio (T t)=Ico a (T t) := by
      ext y
      constructor
      · rintro ⟨hy,hyT⟩; exact ⟨hy.1,hyT⟩
      · intro hy; exact ⟨⟨hy.1,hy.2.le.trans (hTb t ht).2⟩,hy.2⟩
    have he : (fun y : ℝ => G (y,t))=(Iio (T t)).indicator (fun y => W t*P y) := by
      funext y
      dsimp only [G]
      by_cases hh : y<T t
      · rw [ite_eq_left hh,indicator_of_mem (show y ∈ Iio (T t) from hh)]
        ring
      · rw [ite_eq_right hh,indicator_of_notMem (show y ∉ Iio (T t) from hh)]
    rw [he,setIntegral_indicator measurableSet_Iio,hset,integral_const_mul,
      integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le (hTb t ht).1]
  simp_rw [hleft] at hs
  rw [hs]
  exact setIntegral_congr_fun measurableSet_Icc hright

end ErdosOmissionBindings

end

end Erdos970

end OAI
