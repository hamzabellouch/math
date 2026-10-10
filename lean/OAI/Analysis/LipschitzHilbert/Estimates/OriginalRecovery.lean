import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace OAI

/-! The original adjoint sum is estimated on every discarded set.
The central sum enters only on the moving good set; its boundary error
is averaged over the fixed common good set. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert
variable {X E : Type*} [NormedAddCommGroup E]

private theorem three_term_norm (p q w : E) :
    ‖p‖ ≤ ‖p-q‖+‖q-w‖+‖w‖ := by
  calc
    ‖p‖ = ‖(p-q)+(q-w)+w‖ := by congr 1; abel
    _ ≤ ‖(p-q)+(q-w)‖+‖w‖ := norm_add_le _ _
    _ ≤ (‖p-q‖+‖q-w‖)+‖w‖ := by
      linarith [norm_add_le (p-q) (q-w)]

theorem original_recovery_pointwise
    (F Z0 Z : Set X) (hZ0 : Z0 ⊆ F) (hZ : Z ⊆ Z0) (P Q W : X → E) (x : X) :
    F.indicator (fun x => ‖P x‖) x ≤
      (F\Z0).indicator (fun x => ‖P x‖) x +
      (Z0\Z).indicator (fun x => ‖P x‖) x +
      Z0.indicator (fun x => ‖P x-Q x‖) x +
      Z0.indicator (fun x => ‖Q x-W x‖) x + Z.indicator (fun x => ‖W x‖) x := by
  classical
  by_cases hx : x ∈ F
  · by_cases hz0 : x ∈ Z0
    · by_cases hz : x ∈ Z
      · simpa only [indicator_of_mem hx,indicator_of_mem hz0,indicator_of_mem hz,
          indicator_of_notMem (show x ∉ F\Z0 from fun h => h.2 hz0),
          indicator_of_notMem (show x ∉ Z0\Z from fun h => h.2 hz),zero_add]
          using three_term_norm (P x) (Q x) (W x)
      · simp only [indicator_of_mem hx,indicator_of_mem hz0,indicator_of_notMem hz,
          indicator_of_notMem (show x ∉ F\Z0 from fun h => h.2 hz0),
          indicator_of_mem (show x ∈ Z0\Z from ⟨hz0,hz⟩),zero_add,add_zero]
        linarith [norm_nonneg (P x-Q x),norm_nonneg (Q x-W x)]
    · have hz : x ∉ Z := fun h => hz0 (hZ h)
      simp only [indicator_of_mem hx,indicator_of_notMem hz0,indicator_of_notMem hz,
        indicator_of_mem (show x ∈ F\Z0 from ⟨hx,hz0⟩),
        indicator_of_notMem (show x ∉ Z0\Z from fun h => hz0 h.1),add_zero,le_refl]
  · have hz0 : x ∉ Z0 := fun h => hx (hZ0 h)
    have hz : x ∉ Z := fun h => hz0 (hZ h)
    simp only [indicator_of_notMem hx,indicator_of_notMem hz0,indicator_of_notMem hz,
      indicator_of_notMem (show x ∉ F\Z0 from fun h => hx h.1),
      indicator_of_notMem (show x ∉ Z0\Z from fun h => hz0 h.1),add_zero,le_refl]

variable [MeasurableSpace X]

theorem original_recovery_integral
    (μ : Measure X) (F Z0 Z : Set X) (hFm : MeasurableSet F) (hZ0m : MeasurableSet Z0) (hZm : MeasurableSet Z)
    (hZ0 : Z0 ⊆ F) (hZ : Z ⊆ Z0) (P Q W : X → E)
    (hP : IntegrableOn (fun x => ‖P x‖) F μ)
    (hPQ : IntegrableOn (fun x => ‖P x-Q x‖) Z0 μ)
    (hQW : IntegrableOn (fun x => ‖Q x-W x‖) Z0 μ)
    (hW : IntegrableOn (fun x => ‖W x‖) Z μ) :
    (∫ x in F, ‖P x‖ ∂μ) ≤ (∫ x in F\Z0, ‖P x‖ ∂μ) +
      (∫ x in Z0\Z, ‖P x‖ ∂μ) + (∫ x in Z0, ‖P x-Q x‖ ∂μ) +
      (∫ x in Z0, ‖Q x-W x‖ ∂μ) + (∫ x in Z, ‖W x‖ ∂μ) := by
  have h0 : Integrable (F.indicator (fun x => ‖P x‖)) μ :=
    (integrable_indicator_iff hFm).mpr hP
  have h1 : Integrable ((F\Z0).indicator (fun x => ‖P x‖)) μ :=
    (integrable_indicator_iff (hFm.diff hZ0m)).mpr (hP.mono_set sdiff_subset)
  have h2 : Integrable ((Z0\Z).indicator (fun x => ‖P x‖)) μ :=
    (integrable_indicator_iff (hZ0m.diff hZm)).mpr
      (hP.mono_set (fun _ hx => hZ0 hx.1))
  have h3 : Integrable (Z0.indicator (fun x => ‖P x-Q x‖)) μ :=
    (integrable_indicator_iff hZ0m).mpr hPQ
  have h4 : Integrable (Z0.indicator (fun x => ‖Q x-W x‖)) μ :=
    (integrable_indicator_iff hZ0m).mpr hQW
  have h5 : Integrable (Z.indicator (fun x => ‖W x‖)) μ :=
    (integrable_indicator_iff hZm).mpr hW
  have h := integral_mono h0 ((((h1.add h2).add h3).add h4).add h5)
    (original_recovery_pointwise F Z0 Z hZ0 hZ P Q W)
  simp only [Pi.add_apply] at h
  have he5 := integral_add (((h1.add h2).add h3).add h4) h5
  have he4 := integral_add ((h1.add h2).add h3) h4
  have he3 := integral_add (h1.add h2) h3
  have he2 := integral_add h1 h2
  simp only [Pi.add_apply] at he5 he4 he3 he2
  rw [he5,he4,he3,he2] at h
  simpa only [integral_indicator hFm,integral_indicator (hFm.diff hZ0m),
    integral_indicator (hZ0m.diff hZm),integral_indicator hZ0m,integral_indicator hZm] using h

/-- Averaging a pointwise recovery inequality does not require the
moving exceptional sets themselves to be jointly measurable. -/
theorem recover_constant_from_translation_average (R P C : ℝ) (hR : 0 < R)
    (error : ℝ → ℝ) (herror : IntervalIntegrable error volume 0 R)
    (hbound : ∀ origin ∈ Icc 0 R, P ≤ C+error origin) :
    P ≤ C+(∫ origin in (0:ℝ)..R, error origin)/R := by
  have hi := intervalIntegral.integral_mono_on hR.le
    (intervalIntegrable_const (c := P)) ((intervalIntegrable_const (c := C)).add herror) hbound
  rw [intervalIntegral.integral_add (intervalIntegrable_const (c := C)) herror,
    intervalIntegral.integral_const,intervalIntegral.integral_const] at hi
  simp only [sub_zero,smul_eq_mul] at hi
  have hdiv : ((∫ origin in (0:ℝ)..R, error origin)/R)*R =
      (∫ origin in (0:ℝ)..R, error origin) := div_mul_cancel₀ _ hR.ne'
  nlinarith [hi,hdiv]

/-- Fixed exceptions, each moving exception, the mask error, the
averaged boundary error, and the central estimate bound the original sum. -/
theorem recover_original_from_moving_good
    (μ : Measure X) (F Z0 : Set X) (Z : ℝ → Set X)
    (hFm : MeasurableSet F) (hZ0m : MeasurableSet Z0)
    (hZm : ∀ origin, MeasurableSet (Z origin))
    (hZ0 : Z0 ⊆ F) (hZ : ∀ origin, Z origin ⊆ Z0)
    (P Q : X → E) (W : ℝ → X → E)
    (hP : IntegrableOn (fun x => ‖P x‖) F μ)
    (hPQ : IntegrableOn (fun x => ‖P x-Q x‖) Z0 μ)
    (hQW : ∀ origin, IntegrableOn (fun x => ‖Q x-W origin x‖) Z0 μ)
    (hW : ∀ origin, IntegrableOn (fun x => ‖W origin x‖) (Z origin) μ)
    (R Cfixed Cbad Cmask Cboundary Ccentral : ℝ) (hR : 0 < R)
    (hfixed : (∫ x in F\Z0, ‖P x‖ ∂μ) ≤ Cfixed)
    (hbad : ∀ origin, (∫ x in Z0\Z origin, ‖P x‖ ∂μ) ≤ Cbad)
    (hmask : (∫ x in Z0, ‖P x-Q x‖ ∂μ) ≤ Cmask)
    (hcentral : ∀ origin, (∫ x in Z origin, ‖W origin x‖ ∂μ) ≤ Ccentral)
    (herror : IntervalIntegrable (fun origin => ∫ x in Z0, ‖Q x-W origin x‖ ∂μ) volume 0 R)
    (hboundary : (∫ origin in (0:ℝ)..R, ∫ x in Z0, ‖Q x-W origin x‖ ∂μ)/R ≤ Cboundary) :
    (∫ x in F, ‖P x‖ ∂μ) ≤ Cfixed+Cbad+Cmask+Cboundary+Ccentral := by
  have hpoint (origin : ℝ) (_ho : origin ∈ Icc 0 R) :
      (∫ x in F, ‖P x‖ ∂μ) ≤ Cfixed+Cbad+Cmask+Ccentral+
        (∫ x in Z0, ‖Q x-W origin x‖ ∂μ) := by
    have h := original_recovery_integral μ F Z0 (Z origin) hFm hZ0m (hZm origin)
      hZ0 (hZ origin) P Q (W origin) hP hPQ (hQW origin) (hW origin)
    linarith [hbad origin,hcentral origin]
  have h := recover_constant_from_translation_average R (∫ x in F, ‖P x‖ ∂μ)
    (Cfixed+Cbad+Cmask+Ccentral) hR _ herror hpoint
  linarith

end LipschitzHilbert

end

end OAI
