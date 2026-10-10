import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import OAI.Analysis.CircleDomains.Probability.LocalNullImage

namespace OAI

/-! The scalar tail compression used for common-point traces. The null-image
recovery works for arbitrary subsets of the line, by applying the monotone
area formula to a measurable envelope. No analyticity premise is needed. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem null_outside_of_compressed_image_null
    {H : ℝ → ℝ} (hH : Continuous H) (hmono : Monotone H)
    {E S : Set ℝ} (hE : MeasurableSet E)
    (hd : ∀ᵐ x ∂volume, x ∉ E → HasDerivAt H 1 x)
    (hnull : volume (H '' S) = 0) : volume (S \ E) = 0 := by
  let N := toMeasurable volume (H '' S)
  let D := toMeasurable volume {x | x ∉ E ∧ ¬HasDerivAt H 1 x}
  have hN : volume N = 0 := by simpa only [N,measure_toMeasurable] using hnull
  have hD : volume D = 0 := by
    rw [show D = toMeasurable volume {x | x ∉ E ∧ ¬HasDerivAt H 1 x} from rfl,
      measure_toMeasurable]
    simpa only [not_forall,not_imp,exists_prop] using (ae_iff.mp hd)
  let T := (Eᶜ ∩ H ⁻¹' N) \ D
  have hT : MeasurableSet T :=
    (hE.compl.inter (hH.measurable (measurableSet_toMeasurable _ _))).diff
      (measurableSet_toMeasurable _ _)
  have hder (x : ℝ) (hx : x ∈ T) : HasDerivWithinAt H 1 T x := by
    apply HasDerivAt.hasDerivWithinAt
    by_contra hn
    exact hx.2 (subset_toMeasurable volume _ ⟨hx.1.1,hn⟩)
  have ht0 : volume T = 0 := by
    have he := lintegral_deriv_eq_volume_image_of_monotoneOn hT hder (hmono.monotoneOn T)
    have hi : H '' T ⊆ N := by rintro _ ⟨x,hx,rfl⟩; exact hx.1.2
    have hz := measure_mono_null hi hN
    simpa only [ENNReal.ofReal_one,lintegral_const,one_mul,hz,Measure.restrict_apply_univ] using he
  apply measure_mono_null (t := T ∪ D) _ (measure_union_null ht0 hD)
  intro x hx
  by_cases hxD : x ∈ D
  · exact Or.inr hxD
  · exact Or.inl ⟨⟨hx.2,subset_toMeasurable volume _ (mem_image_of_mem H hx.1)⟩,hxD⟩

 def traceCompression (E : Set ℝ) (a t : ℝ) : ℝ :=
  ∫ s in a..t, Eᶜ.indicator (fun _ => (1 : ℝ)) s

 theorem traceCompression_intervalIntegrable {E : Set ℝ} (hE : MeasurableSet E)
    (a b : ℝ) : IntervalIntegrable (Eᶜ.indicator (fun _ => (1 : ℝ))) volume a b :=
  intervalIntegrable_iff.mpr
    ((((locallyIntegrable_const (μ := (volume : Measure ℝ)) (1 : ℝ)).indicator hE.compl).integrableOn_isCompact
      isCompact_uIcc).mono_set uIoc_subset_uIcc)

 theorem traceCompression_sub {E : Set ℝ} (hE : MeasurableSet E) (a x y : ℝ) :
    traceCompression E a y-traceCompression E a x =
      ∫ s in x..y, Eᶜ.indicator (fun _ => (1 : ℝ)) s := by
  exact intervalIntegral.integral_interval_sub_left
    (traceCompression_intervalIntegrable hE a y) (traceCompression_intervalIntegrable hE a x)

 theorem traceCompression_monotone {E : Set ℝ} (hE : MeasurableSet E) (a : ℝ) :
    Monotone (traceCompression E a) := by
  intro x y hxy
  apply sub_nonneg.mp
  rw [traceCompression_sub hE]
  exact intervalIntegral.integral_nonneg_of_forall hxy
    (fun s => indicator_nonneg (fun _ _ => zero_le_one) s)

 theorem traceCompression_lipschitz {E : Set ℝ} (hE : MeasurableSet E) (a : ℝ) :
    LipschitzWith 1 (traceCompression E a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,Real.dist_eq,← Real.norm_eq_abs,traceCompression_sub hE]
  simpa only [NNReal.coe_one,one_mul] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := x) (C := 1)
      (f := Eᶜ.indicator (fun _ => (1 : ℝ)))
      (fun s _ => by simpa using (norm_indicator_le_norm_self (s := Eᶜ) (fun _ => (1 : ℝ)) s))

 theorem traceCompression_ae_deriv {E : Set ℝ} (hE : MeasurableSet E) (a : ℝ) :
    ∀ᵐ x ∂volume, x ∉ E → HasDerivAt (traceCompression E a) 1 x := by
  have hli : LocallyIntegrable (Eᶜ.indicator (fun _ => (1 : ℝ))) volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hE.compl
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hli] with x hx hxe
  have hx' := hx a
  rw [indicator_of_mem (show x ∈ Eᶜ from hxe)] at hx'
  convert hx' using 1
  rfl

 theorem traceCompression_null_recovery {E S : Set ℝ} (hE : MeasurableSet E) (a : ℝ)
    (hn : volume (traceCompression E a '' S) = 0) : volume (S \ E) = 0 :=
  null_outside_of_compressed_image_null (traceCompression_lipschitz hE a).continuous
    (traceCompression_monotone hE a) hE (traceCompression_ae_deriv hE a) hn

 theorem null_of_tail_compressions {E : ℕ → Set ℝ} {S : Set ℝ}
    (hE : ∀ n, MeasurableSet (E n)) (a : ℝ)
    (hnull : ∀ n, volume (traceCompression (E n) a '' S) = 0)
    (htail : Tendsto (fun n => volume (E n)) atTop (𝓝 0)) : volume S = 0 := by
  have hle (n : ℕ) : volume S ≤ volume (E n) := by
    calc
      volume S ≤ volume ((S \ E n) ∪ E n) := measure_mono (by intro x hx; by_cases he : x ∈ E n; exact Or.inr he; exact Or.inl ⟨hx,he⟩)
      _ ≤ volume (S \ E n) + volume (E n) := measure_union_le _ _
      _ = volume (E n) := by rw [traceCompression_null_recovery (hE n) a (hnull n),zero_add]
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds htail hle) bot_le

end CircleDomainRigidity

end

end OAI
