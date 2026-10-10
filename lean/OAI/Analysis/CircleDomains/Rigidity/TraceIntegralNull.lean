import OAI.Analysis.CircleDomains.Rigidity.TraceIntervalPayment
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! A locally integrable line payment kills the outer length of the
image of a null set. Measurability of that image is unnecessary. This
also assembles the local compressed traces for all vanishing tails. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem real_null_image_of_integrable_payment {C V : Set ℝ}
    (hV : IsOpen V) (hC : volume C = 0) (v : ℝ → ℝ)
    {g : ℝ → ℝ} (hg : Integrable g volume) (hgn : ∀ᵐ x ∂volume, 0 ≤ g x)
    (hpay : ∀ x ∈ C ∩ V, ∀ y ∈ C ∩ V, x ≤ y → Icc x y ⊆ V →
      |v y-v x| ≤ ∫ t in Icc x y, g t) : volume (v '' (C ∩ V)) = 0 := by
  let κ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (g x))
  let : IsFiniteMeasure κ := ⟨by
    change volume.withDensity (fun x => ENNReal.ofReal (g x)) univ < ∞
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hg hgn]
    exact ENNReal.ofReal_lt_top⟩
  have hκ : κ (C ∩ V) = 0 :=
    withDensity_absolutelyContinuous volume _ (measure_mono_null inter_subset_left hC)
  apply real_null_image_of_interval_payment κ hV hκ v
  intro x hx y hy hxy hi
  apply (hpay x hx y hy hxy hi).trans_eq
  change (∫ t in Icc x y, g t) = (volume.withDensity (fun x => ENNReal.ofReal (g x)) (Icc x y)).toReal
  rw [withDensity_apply _ measurableSet_Icc]
  exact integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hgn) hg.restrict.aestronglyMeasurable

 theorem null_of_local_compressed_integral_payments {C : Set ℝ}
    (hC : volume C = 0) (b : ℝ → ℝ) {E : ℕ → Set ℝ}
    (hE : ∀ n, MeasurableSet (E n)) (a : ℝ)
    (htail : Tendsto (fun n => volume (E n)) atTop (𝓝 0))
    (hlocal : ∀ n x, x ∈ C → ∃ V : Set ℝ, IsOpen V ∧ x ∈ V ∧
      ∃ g : ℝ → ℝ, Integrable g volume ∧ (∀ᵐ t ∂volume, 0 ≤ g t) ∧
        ∀ y ∈ C ∩ V, ∀ z ∈ C ∩ V, y ≤ z → Icc y z ⊆ V →
          |traceCompression (E n) a (b z)-traceCompression (E n) a (b y)| ≤
            ∫ t in Icc y z, g t) : volume (b '' C) = 0 := by
  apply null_of_tail_compressions hE a _ htail
  intro n
  rw [image_image]
  apply null_image_of_local_null_image
  intro x hx
  obtain ⟨V,hV,hxV,g,hg,hgn,hpay⟩ := hlocal n x hx
  exact ⟨V,hV,hxV,real_null_image_of_integrable_payment hV hC
    (fun y => traceCompression (E n) a (b y)) hg hgn hpay⟩

end CircleDomainRigidity

end

end OAI
