import OAI.Analysis.FiniteFactor.Sampling.Rectangle
import Mathlib.MeasureTheory.Integral.Layercake

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

/-- A bounded measurable real function on a finite measure space is integrable. -/
theorem sampling_integrable_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable f μ := by
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  exact Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hb x)

/-- Finite layer-cake formula for a product, valid even for a singular joint law. -/
theorem sampling_product_layerCake {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (C : ℝ) (_hC : 0 ≤ C)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ C) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ C) :
    (∫ x, f x*g x ∂μ) =
      ∫ r in Set.Ioc 0 C, ∫ t in Set.Ioc 0 C,
        (μ {x | r ≤ f x ∧ t ≤ g x}).toReal := by
  let ν := volume.restrict (Set.Ioc 0 C)
  let K : (ℝ × ℝ) × Ω → ℝ := fun p =>
    if p.1.1 ≤ f p.2 ∧ p.1.2 ≤ g p.2 then 1 else 0
  have hK : Measurable K := measurable_const.ite
    ((measurableSet_le measurable_fst.fst (hf.comp measurable_snd)).inter
      (measurableSet_le measurable_fst.snd (hg.comp measurable_snd))) measurable_const
  have hKb (p) : |K p| ≤ 1 := by dsimp [K]; split_ifs <;> norm_num
  have hKi := sampling_integrable_bounded ((ν.prod ν).prod μ) K hK 1 hKb
  have hpoint (x : Ω) : (∫ p, K (p,x) ∂ν.prod ν) = f x*g x := by
    have hik : Integrable (fun p => K (p,x)) (ν.prod ν) :=
      sampling_integrable_bounded (ν.prod ν) _
        (hK.comp (measurable_id.prodMk measurable_const)) 1 (fun p => hKb (p,x))
    rw [integral_prod _ hik]
    have he (r t : ℝ) : K ((r,t),x) =
        (Set.Iic (f x)).indicator (fun _ => (1 : ℝ)) r *
        (Set.Iic (g x)).indicator (fun _ => (1 : ℝ)) t := by
      simp only [K,Set.indicator,Set.mem_Iic]; split_ifs <;> simp_all
    simp_rw [he,integral_const_mul,integral_mul_const]
    have hv (a : ℝ) (ha : 0 ≤ a ∧ a ≤ C) :
        (∫ r, (Set.Iic a).indicator (fun _ => (1 : ℝ)) r ∂ν) = a := by
      rw [integral_indicator measurableSet_Iic]
      simp only [integral_const,smul_eq_mul,mul_one,measureReal_def]
      dsimp [ν]
      rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,
        Measure.restrict_apply measurableSet_Iic]
      have he : Set.Iic a ∩ Set.Ioc 0 C = Set.Ioc 0 a := by
        ext r; simp only [Set.mem_inter_iff,Set.mem_Iic,Set.mem_Ioc]
        constructor
        · intro h; exact ⟨h.2.1,h.1⟩
        · intro h; exact ⟨h.2,h.1,h.2.trans ha.2⟩
      rw [he,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal ha.1]
    rw [hv _ (hfb x),hv _ (hgb x)]
  calc
    _ = ∫ x, ∫ p, K (p,x) ∂ν.prod ν ∂μ := by simp_rw [hpoint]
    _ = ∫ p, ∫ x, K (p,x) ∂μ ∂ν.prod ν := (integral_integral_swap hKi).symm
    _ = ∫ r, ∫ t, ∫ x, K ((r,t),x) ∂μ ∂ν ∂ν :=
      integral_prod _ hKi.integral_prod_left
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with r
      apply integral_congr_ae
      filter_upwards [] with t
      have he : (fun x => K ((r,t),x)) =
          {x | r ≤ f x ∧ t ≤ g x}.indicator (fun _ => (1 : ℝ)) := by funext x; simp [K,Set.indicator]
      have hm : MeasurableSet {x | r ≤ f x ∧ t ≤ g x} :=
        (measurableSet_le measurable_const hf).inter (measurableSet_le measurable_const hg)
      rw [he,integral_indicator hm]
      simp [measureReal_def]

end
end FiniteFactor

end OAI
